# INTSECA

This repository contains Mathematic**A** notebooks that provide details of applying twisted **INT**er**SEC**tion theory to derive differential equations for cosmological correlators.

This package implements the twisted intersection-theory machinery to:

- generate master integrals for the given twisted integral,
- reduce to the master integrals of physical interest
- build the associated (canonical) differential system (A-matrix), and
- derive scalar ODEs for correlators via kinematic flows.

---

## Contents

- `INTSECA.wl` — Wolfram Language package (version banner prints `INTSECA 1.2.0`).
- `notebooks/three-site.nb` — Example driver for the 3-site chain (the transcript below mirrors the steps).
- `storage/` — Cached results used for basis reduction.

---

## Quick start (3‑site chain)

```wl
SetDirectory[NotebookDirectory[]];
<< INTSECA.wl
(* prints: INTSECA 1.2.0 *)

(* Model setup *)
dim = 3; (* integral dimension *)
nkin = 5; 
kin = {X1, X2, X3, Y12, Y23};

(* Untwisted hyperplanes B_i, in projective coordinates *)
nBplane = 6;
B[1] = {1, 0, 0, X1 + Y12};
B[2] = {0, 1, 0, X2 + Y12 + Y23};
B[3] = {0, 0, 1, X3 + Y23};
B[4] = {1, 1, 1, X1 + X2 + X3};
B[5] = {1, 1, 0, X1 + X2 + Y23};
B[6] = {0, 1, 1, X2 + X3 + Y12};

(* Twisted hyperplanes T_a and powers *)
nTplane = 3;
T[1] = {1, 0, 0, 0}; T[2] = {0, 1, 0, 0}; T[3] = {0, 0, 1, 0};
powers = {e, e, e};

(* Wavefunction (twisted cocycle) *)
psi = 〈 1, 2, 3 〉 - 〈 1, 2, 6 〉 - 〈 1, 3, 4 〉 + 〈 1, 3, 5 〉 + 〈 1, 3, 6 〉 - 〈 1, 4, 5 〉 - 〈 2, 3, 5 〉 + 〈 2, 4, 5 〉 - 〈 2, 4, 6 〉 + 〈 3, 4, 6 〉;

```

> **Outcome for the 3‑site chain**
>
> - Physical basis dimension: **16**  
> - Alphabet size: **13** letters:  
>   `{X1+X2+X3, X1±Y12, X2+X3±Y12, X1+X2±Y23, X3±Y23, X2±Y12±Y23}` (appearing as `Log[...]`).  
> - Closure level: **3**.  
> - Canonical A-matrices: `Amatrix16` (16×16).

---