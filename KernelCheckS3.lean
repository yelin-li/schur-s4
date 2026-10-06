import CertificateS3

set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

/-! Does the *kernel* accept the certificate without trusting the compiler?

Measured: with the default heartbeat budget the kernel evaluation does not get
through `checkProof cert3` (timeout at 200000 heartbeats, ~13 s).  This file
raises the budget so the experiment can be run to completion; the certificate is
otherwise checked with `native_decide` in `CertCheckS3.lean`.
-/

open Resolution

example : Resolution.checkProof Resolution.cert3 = true := by decide
