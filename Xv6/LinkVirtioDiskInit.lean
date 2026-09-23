/-
`virtio_disk_init`'s interface, instantiated from its proof.  It calls
`initlock`, `kalloc` and `memset`; the three interfaces stay parameters
here, so a client may close them with the linked ones (`LinkInitlock`,
`LinkKalloc`, `LinkMemset`) or with its own.  `Xv6.DISK_INIT_WM` is the
one TSO fact about the zeroing stores that this port leaves open (see its
doc comment in `Xv6/DiskAcc.lean`).
-/
import Xv6.ProofVirtioDiskInit

namespace Xv6

/-- The proved `virtio_disk_init` interface, given `initlock`, `kalloc`
and `memset`. -/
theorem VirtioDiskInit (WM : DISK_INIT_WM) (IL : INITLOCK) (KAL : KALLOC) (MS : MEMSET) :
    VIRTIO_DISK_INIT :=
  virtio_disk_init_proof WM IL KAL MS

end Xv6
