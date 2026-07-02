# T08: bridge+decode invariant

## Statement
∀ u,anchor,c1_t,c2,σ,DDM:
  decode(bridge(encode(op), ...), ...) = u

## Rust Source
`chaosvm-core/src/conj_vm/sem_share.rs:95-134`

## Proof
Algebraic XOR cancellation of 4 matching P-term pairs.

## Status
✅ Full proof in SemShare.lean (swap_pair, hA_cancel, hBC, h_inner, h_rest)

