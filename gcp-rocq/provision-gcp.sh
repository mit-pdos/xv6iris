#!/usr/bin/env bash
# Build the shared Rocq build VM from nothing: firewall, persistent data disk,
# Spot instance, idle-shutdown service, and the shared opam switch.
#
# Safe to re-run. Every step checks for what it needs before creating it, so
# this doubles as the repair tool if the instance is ever deleted: the data
# disk survives and gets reattached, opam switch and work trees intact.
set -euo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=config.sh
source "$HERE/config.sh"

say()  { printf '\033[1;34m==>\033[0m %s\n' "$*"; }
warn() { printf '\033[1;33m warn:\033[0m %s\n' "$*" >&2; }
die()  { printf '\033[1;31merror:\033[0m %s\n' "$*" >&2; exit 1; }

g() { gcloud --project="$PROJECT" "$@"; }

# Temp files are cleaned up from a single EXIT trap. A per-function RETURN trap
# looks tidier but stays registered after that function returns, so it fires
# again on the next function return -- when its locals are gone, and set -u
# turns that into a fatal error after the work has already succeeded.
declare -a TMPFILES=()
cleanup() { (( ${#TMPFILES[@]} )) && rm -f "${TMPFILES[@]}"; return 0; }
trap cleanup EXIT

# ---------------------------------------------------------------- preflight
preflight() {
  command -v gcloud >/dev/null || die "gcloud not found on PATH"
  command -v rsync  >/dev/null || die "rsync not found on PATH"
  [[ -f "$SSH_KEY" ]] || die "ssh key $SSH_KEY not found (generate with ssh-keygen -t ed25519)"
  [[ -f "$SSH_KEY.pub" ]] || die "ssh public key $SSH_KEY.pub not found"

  g auth print-access-token >/dev/null 2>&1 \
    || die "gcloud is not authenticated for project $PROJECT"

  if ! g compute regions describe "$REGION" >/dev/null 2>&1; then
    die "cannot reach Compute Engine API in $REGION (is compute.googleapis.com enabled?)"
  fi
}

# Pick a zone that actually offers the machine type. Availability is per-zone,
# not per-region, so this avoids a confusing failure at create time.
resolve_zone() {
  if [[ -n "$ZONE" ]]; then
    say "using zone $ZONE"
    return
  fi
  say "looking for a zone in $REGION offering $MACHINE_TYPE"
  # Anchored regex rather than 'name=': gcloud warns that '=' comparison
  # semantics are changing, and the regex form is unambiguous today and later.
  ZONE="$(g compute machine-types list \
            --filter="name~^$MACHINE_TYPE\$ AND zone~^$REGION-" \
            --format='value(zone.basename())' 2>/dev/null | sort | head -n1)"
  [[ -n "$ZONE" ]] || die "no zone in $REGION offers $MACHINE_TYPE"
  say "selected zone $ZONE"
}

# ---------------------------------------------------------------- firewall
ensure_firewall() {
  if g compute firewall-rules describe "$FIREWALL_RULE" >/dev/null 2>&1; then
    say "firewall rule $FIREWALL_RULE already exists"
    return
  fi
  say "creating firewall rule $FIREWALL_RULE (tcp:22 from $SSH_SOURCE_RANGES)"
  g compute firewall-rules create "$FIREWALL_RULE" \
    --direction=INGRESS --action=ALLOW --rules=tcp:22 \
    --source-ranges="$SSH_SOURCE_RANGES" \
    --target-tags=rocq-builder \
    --description="SSH to the Rocq build VM"
}

# ---------------------------------------------------------------- data disk
ensure_data_disk() {
  if g compute disks describe "$DATA_DISK" --zone="$ZONE" >/dev/null 2>&1; then
    say "data disk $DATA_DISK already exists"
    return
  fi
  say "creating $DATA_DISK_SIZE data disk $DATA_DISK"
  g compute disks create "$DATA_DISK" \
    --zone="$ZONE" --size="$DATA_DISK_SIZE" --type="$DATA_DISK_TYPE" \
    --description="Rocq opam root and per-agent work trees"
}

# ---------------------------------------------------------------- instance
# Runs on every boot. Deliberately limited to things that must be true for the
# machine to be usable: the data disk mounted, and idle shutdown armed. Heavy
# package installation lives in bootstrap_vm so it does not repeat each boot.
render_startup_script() {
  cat <<STARTUP
#!/bin/bash
set -x
DATA_DEV=/dev/disk/by-id/google-$DATA_DISK
MNT=$DATA_MOUNT
IDLE_LIMIT=$IDLE_LIMIT

mkdir -p "\$MNT"

# Format only if the disk has no filesystem. Never reformat: this disk is the
# thing the whole design exists to preserve.
#
# Lazy inode/journal init is the ext4 default and is what we want: eager init
# (lazy_itable_init=0) zeroes all 65M inode tables up front, which takes many
# minutes on a 1TB volume, versus seconds when the kernel does it in the
# background. GCP's docs suggest the eager flags; there is no benefit here.
if ! blkid "\$DATA_DEV" >/dev/null 2>&1; then
  mkfs.ext4 -m 0 -F -E lazy_itable_init=1,lazy_journal_init=1,discard "\$DATA_DEV"
fi

UUID=\$(blkid -s UUID -o value "\$DATA_DEV")
if ! grep -q "\$UUID" /etc/fstab; then
  echo "UUID=\$UUID \$MNT ext4 discard,defaults,nofail 0 2" >> /etc/fstab
fi
mountpoint -q "\$MNT" || mount "\$MNT"

mkdir -p "\$MNT/trees" "\$MNT/opam" "\$MNT/shared"
chown "$SSH_USER:$SSH_USER" "\$MNT" "\$MNT/trees" "\$MNT/opam" "\$MNT/shared" 2>/dev/null || true

# A project's opam switch may need to live at the same absolute path as on the
# dev machine, because .vo only load against a byte-identical switch: two opam
# builds of the same Rocq version embed different build data and Rocq then
# rejects the artifacts with "inconsistent assumptions over library ...".
# Copying the dev switch to the identical path is what makes pulled .vo usable
# locally. Bind-mounted off the data disk so it survives an instance rebuild.
mkdir -p /shared
if ! grep -q "^\$MNT/shared /shared" /etc/fstab; then
  echo "\$MNT/shared /shared none bind,nofail 0 0" >> /etc/fstab
fi
mountpoint -q /shared || mount --bind "\$MNT/shared" /shared

# --- idle shutdown -----------------------------------------------------
cat > /usr/local/sbin/rocq-idle-check <<'CHECK'
#!/bin/bash
# Power the VM off after a sustained idle period. Runs from a systemd timer.
STAMP=/run/rocq-last-active
KEEP=__MNT__/.keep-awake
LIMIT=__LIMIT__
now=\$(date +%s)
[ -f "\$STAMP" ] || echo "\$now" > "\$STAMP"

busy=0
# Escape hatch: touch the keep-awake file to pin the VM up.
[ -e "\$KEEP" ] && busy=1
# Any live ssh session, including non-interactive 'ssh host cmd' (which shows
# up as user@notty and leaves no utmp entry, so 'who' would miss it).
pgrep -f 'sshd(-session)?: .*@' >/dev/null 2>&1 && busy=1
# Detached work started with nohup keeps the machine alive on its own.
for p in coqc coqtop coqchk rocq rocqc rocqchk make dune opam rsync ocamlopt ocamlc; do
  pgrep -x "\$p" >/dev/null 2>&1 && { busy=1; break; }
done

if [ "\$busy" = 1 ]; then
  echo "\$now" > "\$STAMP"
  exit 0
fi

last=\$(cat "\$STAMP" 2>/dev/null || echo "\$now")
if [ \$(( now - last )) -ge "\$LIMIT" ]; then
  logger -t rocq-idle "idle \$(( now - last ))s >= \${LIMIT}s, powering off"
  /sbin/shutdown -h now "rocq idle shutdown"
fi
CHECK
sed -i "s#__MNT__#\$MNT#; s#__LIMIT__#\$IDLE_LIMIT#" /usr/local/sbin/rocq-idle-check
chmod +x /usr/local/sbin/rocq-idle-check

cat > /etc/systemd/system/rocq-idle-shutdown.service <<'UNIT'
[Unit]
Description=Power off the Rocq build VM when idle
[Service]
Type=oneshot
ExecStart=/usr/local/sbin/rocq-idle-check
UNIT

cat > /etc/systemd/system/rocq-idle-shutdown.timer <<UNIT
[Unit]
Description=Periodic idle check for the Rocq build VM
[Timer]
OnBootSec=$IDLE_CHECK_INTERVAL
OnUnitActiveSec=$IDLE_CHECK_INTERVAL
[Install]
WantedBy=timers.target
UNIT

# /run is tmpfs, so the activity stamp resets on every boot. That is what we
# want: a machine that just came up is not instantly eligible for shutdown.
date +%s > /run/rocq-last-active
systemctl daemon-reload
systemctl enable --now rocq-idle-shutdown.timer
STARTUP
}

# The `ssh-keys` metadata value: $SSH_KEY.pub plus every key in
# $EXTRA_AUTHORIZED_KEYS, as `user:<key>` lines.
#
# authorized_keys is a richer format than this metadata accepts, so the filter
# is not cosmetic. Comments and blank lines are dropped, and so is any entry
# carrying OPTIONS (`command="..." ssh-ed25519 ...`, `restrict,...`): the guest
# agent writes each metadata line into authorized_keys verbatim, so an options
# prefix would smuggle a forced command onto the VM under a key that looks
# ordinary here -- and a from="..." restriction naming the local network would
# silently not apply on the VM, which is the more likely way to get this wrong.
# Keeping only bare `<type> <base64> [comment]` lines makes what is authorized
# on the VM exactly what it looks like.
#
# Deduplication is on type+base64, ignoring the comment, so $SSH_KEY.pub
# appearing in authorized_keys too (the usual case when you can ssh to this
# machine) does not double the entry.
render_ssh_keys() {
  {
    cat "$SSH_KEY.pub"
    [[ -r "$EXTRA_AUTHORIZED_KEYS" ]] && cat "$EXTRA_AUTHORIZED_KEYS"
  } 2>/dev/null | awk -v user="$SSH_USER" '
    $1 ~ /^(ssh-(rsa|dss|ed25519)|ecdsa-sha2-nistp(256|384|521)|sk-(ssh-ed25519|ecdsa-sha2-nistp256)@openssh\.com)$/ &&
      NF >= 2 && !seen[$1 " " $2]++ { print user ":" $0 }'
}

# Metadata is set at create time only, so this is what carries a key change to
# a VM that already exists -- and add-metadata REPLACES the ssh-keys value
# wholesale, which is what makes it idempotent rather than cumulative. The
# guest agent rewrites the VM's authorized_keys within a few seconds; nothing
# needs restarting. A key REMOVED from the local authorized_keys is revoked on
# the VM by the same mechanism, so this is the only place keys are decided.
ensure_ssh_keys() {
  local keys want have
  keys="$(mktemp)"; TMPFILES+=( "$keys" )
  render_ssh_keys > "$keys"
  want="$(cat "$keys")"
  [[ -n "$want" ]] || die "no usable public keys (checked $SSH_KEY.pub and $EXTRA_AUTHORIZED_KEYS)"

  have="$(g compute instances describe "$INSTANCE" --zone="$ZONE" \
            --format='value(metadata.items.filter("key:ssh-keys").extract("value").flatten())' 2>/dev/null || true)"
  if [[ "$have" == "$want" ]]; then
    say "ssh keys already current ($(wc -l < "$keys") authorized)"
    return
  fi
  say "updating ssh-keys metadata ($(wc -l < "$keys") authorized for $SSH_USER)"
  g compute instances add-metadata "$INSTANCE" --zone="$ZONE" \
    --metadata-from-file="ssh-keys=$keys" >/dev/null
}

ensure_instance() {
  if g compute instances describe "$INSTANCE" --zone="$ZONE" >/dev/null 2>&1; then
    say "instance $INSTANCE already exists"
    return
  fi

  local startup keys
  startup="$(mktemp)"; keys="$(mktemp)"
  TMPFILES+=( "$startup" "$keys" )
  render_startup_script > "$startup"
  render_ssh_keys > "$keys"

  # A new instance has a new host key. Since we pin host keys to the instance
  # name via HostKeyAlias (so a changing external IP is not mistaken for an
  # attack), a stale entry here would make every later ssh fail with
  # IDENTIFICATION HAS CHANGED. Drop it as part of creating the machine.
  if [[ -f "$STATE_DIR/known_hosts" ]]; then
    ssh-keygen -R "$INSTANCE" -f "$STATE_DIR/known_hosts" >/dev/null 2>&1 || true
  fi

  say "creating $MACHINE_TYPE ($PROVISIONING_MODEL) instance $INSTANCE in $ZONE"
  g compute instances create "$INSTANCE" \
    --zone="$ZONE" \
    --machine-type="$MACHINE_TYPE" \
    --provisioning-model="$PROVISIONING_MODEL" \
    --instance-termination-action="$TERMINATION_ACTION" \
    --image-family="$BOOT_IMAGE_FAMILY" \
    --image-project="$BOOT_IMAGE_PROJECT" \
    --boot-disk-size="$BOOT_DISK_SIZE" \
    --boot-disk-type="$BOOT_DISK_TYPE" \
    --boot-disk-device-name="$INSTANCE-boot" \
    --disk="name=$DATA_DISK,device-name=$DATA_DISK,mode=rw,auto-delete=no" \
    --tags=rocq-builder \
    --metadata-from-file="ssh-keys=$keys,startup-script=$startup" \
    --metadata=enable-oslogin=FALSE \
    --labels=purpose=rocq-build
}

start_if_stopped() {
  local status
  status="$(g compute instances describe "$INSTANCE" --zone="$ZONE" --format='value(status)')"
  if [[ "$status" != "RUNNING" ]]; then
    say "instance is $status, starting it"
    g compute instances start "$INSTANCE" --zone="$ZONE"
  fi
}

instance_ip() {
  g compute instances describe "$INSTANCE" --zone="$ZONE" \
    --format='value(networkInterfaces[0].accessConfigs[0].natIP)'
}

# HostKeyAlias pins the host key to the instance name rather than its address.
# The external IP changes on every stop/start; without this every restart would
# look like a man-in-the-middle and break the connection.
ssh_opts() {
  mkdir -p "$STATE_DIR"
  printf '%s\n' \
    -i "$SSH_KEY" \
    -o "HostKeyAlias=$INSTANCE" \
    -o "UserKnownHostsFile=$STATE_DIR/known_hosts" \
    -o StrictHostKeyChecking=accept-new \
    -o ControlMaster=auto \
    -o "ControlPath=$STATE_DIR/cm-$INSTANCE" \
    -o ControlPersist=10m \
    -o ServerAliveInterval=30 \
    -o LogLevel=ERROR
}

wait_for_ssh() {
  local ip deadline
  ip="$(instance_ip)"
  [[ -n "$ip" ]] || die "instance has no external IP"
  say "waiting for sshd on $ip"
  mapfile -t opts < <(ssh_opts)
  deadline=$(( SECONDS + 300 ))
  while (( SECONDS < deadline )); do
    if ssh "${opts[@]}" -o ConnectTimeout=5 "$SSH_USER@$ip" true 2>/dev/null; then
      say "ssh is up"
      return
    fi
    sleep 5
  done
  die "timed out waiting for ssh on $ip"
}

# sshd comes up well before the boot-time startup script finishes, and on first
# boot that script has a 1TB filesystem to create. Anything needing the data
# disk must block on this; without it the opam step races the format and fails
# whenever mkfs happens to lose.
wait_for_startup_script() {
  local ip state deadline
  ip="$(instance_ip)"
  mapfile -t opts < <(ssh_opts)
  say "waiting for the boot-time startup script (first boot formats $DATA_DISK_SIZE)"
  deadline=$(( SECONDS + 1800 ))
  while (( SECONDS < deadline )); do
    state="$(ssh "${opts[@]}" -o ConnectTimeout=10 "$SSH_USER@$ip" \
              'systemctl is-active google-startup-scripts.service 2>/dev/null' 2>/dev/null || true)"
    if [[ -n "$state" && "$state" != "activating" ]]; then
      if ssh "${opts[@]}" "$SSH_USER@$ip" "mountpoint -q $(printf %q "$DATA_MOUNT")" 2>/dev/null; then
        say "startup script finished; $DATA_MOUNT is mounted"
        return
      fi
      die "startup script ended but $DATA_MOUNT is not mounted. Inspect with:
  gcloud compute ssh $INSTANCE --zone=$ZONE -- sudo journalctl -u google-startup-scripts"
    fi
    sleep 10
  done
  die "timed out waiting for the startup script to finish"
}

# ---------------------------------------------------------------- OS packages
# Guarded by a sentinel on the *boot* disk: reinstalling these is only needed
# when the instance itself is rebuilt.
bootstrap_vm() {
  local ip; ip="$(instance_ip)"
  mapfile -t opts < <(ssh_opts)
  say "installing OS packages"
  ssh "${opts[@]}" "$SSH_USER@$ip" \
    "EXTRA_APT_PACKAGES=$(printf %q "$EXTRA_APT_PACKAGES") bash -s" <<'REMOTE'
set -euo pipefail
SENTINEL=/var/lib/rocq-bootstrap-done
if [[ -f "$SENTINEL" ]]; then
  echo "OS packages already installed, skipping"
  exit 0
fi
export DEBIAN_FRONTEND=noninteractive
sudo -E apt-get update -qq
# shellcheck disable=SC2086  # word splitting of the package list is intended
sudo -E apt-get install -y -qq \
  build-essential git m4 unzip pkg-config curl ca-certificates \
  rsync bubblewrap libgmp-dev python3 time opam $EXTRA_APT_PACKAGES
sudo touch "$SENTINEL"
echo "OS packages installed"
REMOTE
}

# ---------------------------------------------------------------- opam env
# No opam init/repository/install here -- see the comment on OPAM_ROOT in
# config.sh. This just points every future login shell's OPAMROOT at the data
# disk's opam root, so `opam exec --switch=/shared/xv6rocq --` (what the
# Makefile actually runs) has a root to resolve that switch against. Cheap and
# idempotent, so it runs on every provision rather than being sentinel-gated.
wire_opam_env() {
  local ip; ip="$(instance_ip)"
  mapfile -t opts < <(ssh_opts)
  say "wiring OPAMROOT into login shells"
  ssh "${opts[@]}" "$SSH_USER@$ip" \
    "sudo tee /etc/profile.d/rocq-opam.sh >/dev/null" <<PROFILE
export OPAMROOT=$OPAM_ROOT
PROFILE
}

# ---------------------------------------------------------------- summary
summary() {
  local ip; ip="$(instance_ip)"
  cat <<EOF

$(say "provisioning complete")

  instance   $INSTANCE ($MACHINE_TYPE, $PROVISIONING_MODEL, termination=$TERMINATION_ACTION)
  zone       $ZONE
  address    $ip   (ephemeral: it changes on every restart, which is why
                    run-on-gcp looks it up each time and pins the host key
                    to the instance name)
  data disk  $DATA_DISK ($DATA_DISK_SIZE) mounted at $DATA_MOUNT
  opam root  $OPAM_ROOT (OPAMROOT wired into login shells; the switch
             itself, /shared/xv6rocq, is not installed here -- copy it onto
             this disk, see claude-notes/remote-build-gcp.md)
  work trees $TREES_DIR
  idle       powers off after ${IDLE_LIMIT}s idle; touch $DATA_MOUNT/.keep-awake to pin it up

next:
  cd /path/to/your/proof/tree
  $HERE/run-on-gcp make -j 36

EOF
}

main() {
  preflight
  resolve_zone
  ensure_firewall
  ensure_data_disk
  ensure_instance
  ensure_ssh_keys
  start_if_stopped
  wait_for_ssh
  # apt needs no data disk, so run it first and let it overlap with the format.
  bootstrap_vm
  wait_for_startup_script
  wire_opam_env
  summary
}

main "$@"
