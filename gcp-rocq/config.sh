# shellcheck shell=bash
# shellcheck disable=SC2034  # every value here is consumed by the sourcing script
#
# Shared configuration for provision-gcp.sh and run-on-gcp.
# Sourced by both. Override any value via the environment.

# ---- GCP placement -----------------------------------------------------
PROJECT="${ROCQ_PROJECT:-gcp-jplu8a}"
REGION="${ROCQ_REGION:-us-east4}"
# Leave ZONE empty to auto-pick the first zone in REGION that offers MACHINE_TYPE.
ZONE="${ROCQ_ZONE:-}"

INSTANCE="${ROCQ_INSTANCE:-rocq-builder}"
# Sized from a measured build: the 1092-file xv6iris development peaked at
# ~119 concurrent workers with a ~1min serial tail, so 180 vCPU sat mostly
# idle. 90 costs half as much ($1.68 vs $3.37/hr spot) for near-identical
# wall-clock. Revisit if several agents routinely build at once.
MACHINE_TYPE="${ROCQ_MACHINE_TYPE:-c3d-standard-90}"

# SPOT + STOP means preemption halts the VM instead of deleting it, so both
# disks survive and the instance can simply be started again.
PROVISIONING_MODEL="${ROCQ_PROVISIONING_MODEL:-SPOT}"
TERMINATION_ACTION="${ROCQ_TERMINATION_ACTION:-STOP}"

# ---- disks -------------------------------------------------------------
# Match the dev container's Ubuntu release. This is not cosmetic: the VM's
# cross-compiler must be the same version as the one that produced any tracked
# generated sources, or a rebuild yields a different binary and every proof
# naming a symbol address breaks. 24.04 ships riscv64 gcc 13.3.0 / binutils
# 2.42; 26.04 ships 15.2.0 / 2.46, which is what the container has.
BOOT_IMAGE_FAMILY="${ROCQ_BOOT_IMAGE_FAMILY:-ubuntu-2604-lts-amd64}"
BOOT_IMAGE_PROJECT="${ROCQ_BOOT_IMAGE_PROJECT:-ubuntu-os-cloud}"
BOOT_DISK_SIZE="${ROCQ_BOOT_DISK_SIZE:-100GB}"
BOOT_DISK_TYPE="${ROCQ_BOOT_DISK_TYPE:-pd-balanced}"

# The persistent data disk. Holds the opam root and every agent's work tree,
# so it survives preemption *and* a full rebuild of the instance.
DATA_DISK="${ROCQ_DATA_DISK:-rocq-data}"
DATA_DISK_SIZE="${ROCQ_DATA_DISK_SIZE:-1000GB}"
DATA_DISK_TYPE="${ROCQ_DATA_DISK_TYPE:-pd-balanced}"
DATA_MOUNT="${ROCQ_DATA_MOUNT:-/mnt/rocq}"

# ---- access ------------------------------------------------------------
SSH_USER="${ROCQ_SSH_USER:-rocq}"
SSH_KEY="${ROCQ_SSH_KEY:-$HOME/.ssh/id_ed25519}"
FIREWALL_RULE="${ROCQ_FIREWALL_RULE:-rocq-allow-ssh}"
SSH_SOURCE_RANGES="${ROCQ_SSH_SOURCE_RANGES:-0.0.0.0/0}"

# Additional public keys to authorize for $SSH_USER, one per line in
# authorized_keys format. Whoever can already reach this machine can reach the
# VM, so mirroring the local authorized_keys is what lets a human ssh in
# directly to look at a build the agent started. Missing file = just $SSH_KEY.
# Set to /dev/null to authorize nothing but $SSH_KEY.
EXTRA_AUTHORIZED_KEYS="${ROCQ_EXTRA_AUTHORIZED_KEYS:-$HOME/.ssh/authorized_keys}"

# ---- idle shutdown -----------------------------------------------------
# Seconds of continuous inactivity before the VM powers itself off.
IDLE_LIMIT="${ROCQ_IDLE_LIMIT:-3600}"
IDLE_CHECK_INTERVAL="${ROCQ_IDLE_CHECK_INTERVAL:-5min}"

# ---- toolchain ---------------------------------------------------------
OCAML_VERSION="${ROCQ_OCAML_VERSION:-4.14.2}"
# Base packages installed into the shared switch. Project-specific
# dependencies are better installed later via: run-on-gcp opam install ...
ROCQ_PACKAGES="${ROCQ_PACKAGES:-rocq-prover}"
EXTRA_OPAM_PACKAGES="${ROCQ_EXTRA_OPAM_PACKAGES:-}"
# Extra system packages. The riscv64 cross toolchain is here because xv6iris
# disassembles a real kernel ELF into Rocq; harmless for projects that do not.
EXTRA_APT_PACKAGES="${ROCQ_EXTRA_APT_PACKAGES:-gcc-riscv64-linux-gnu binutils-riscv64-linux-gnu}"
OPAM_ROOT="${ROCQ_OPAM_ROOT:-$DATA_MOUNT/opam}"
OPAM_SWITCH="${ROCQ_OPAM_SWITCH:-default}"

# ---- sync --------------------------------------------------------------
TREES_DIR="${ROCQ_TREES_DIR:-$DATA_MOUNT/trees}"

# Compare file *contents* rather than mtimes when deciding what to send.
# Paired with --no-times in run-on-gcp, this is what keeps incremental make
# correct: transferred files get the VM's write time (so make rebuilds them),
# untransferred files keep their old timestamps (so make skips them), and the
# local clock never enters into it. Turning this off is faster on very large
# trees but reintroduces the backwards-mtime failure mode described there.
USE_CHECKSUM="${ROCQ_USE_CHECKSUM:-1}"

# Honour .gitignore when syncing. This matters more than it looks: a project
# may clone or build things on the VM that do not exist locally (xv6iris does
# exactly this with xv6-riscv/ and sail-riscv/). Without this, --delete would
# wipe them on the next sync. Excluded paths are protected from deletion, and
# git's ignore set is precisely the "generated, not source" set.
USE_GITIGNORE="${ROCQ_USE_GITIGNORE:-1}"

# Syncing .git costs real time under --checksum (packfiles get hashed every
# run) and remote builds rarely need it. Set to 1 if your Makefile shells out
# to git for version stamping.
SYNC_GIT="${ROCQ_SYNC_GIT:-0}"

# Build artifacts live only on the VM. They are excluded from the push, which
# also protects them from --delete: rsync will not delete an excluded file.
# Getting this wrong wipes every .vo on the first sync and turns every build
# into a full rebuild.
ROCQ_EXCLUDES=(
  '*.vo' '*.vos' '*.vok' '*.vio' '*.glob'
  '.coq-native/' '*.aux' '.*.aux'
  '*.cmi' '*.cmx' '*.cmo' '*.cma' '*.cmxa' '*.cmxs' '*.o' '*.a' '*.annot'
  '_build/' '.lia.cache' '.nia.cache'
  '*.swp' '*~' '.#*' '#*#' '.DS_Store'
)

# State for ssh control sockets and the pinned host key.
# Artifacts pulled back by --pull-vo. These are precisely the files the push
# excludes: the VM owns them, and this is how you get them locally so a
# single-file `rocq compile` can find its dependencies' .vo without rebuilding
# the whole tree here. The CoqMakefile trio comes along so a local `make` works
# too; all of it is gitignored, so it never dirties the checkout.
ARTIFACT_PATTERNS=(
  '*.vo' '*.vos' '*.vok' '*.glob' '.*.aux'
  'CoqMakefile' 'CoqMakefile.conf' '.CoqMakefile.d'
)

STATE_DIR="${ROCQ_STATE_DIR:-$HOME/.cache/run-on-gcp}"
