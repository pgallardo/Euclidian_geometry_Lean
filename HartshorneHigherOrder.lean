import Mathlib
set_option quotPrecheck false
--Ch 2. HILBERT'S AXIOMS
--INTRO:
--Hartshorne presents Hilbert's axioms in higher order logic.
--`Point` is a primitive ``sort (or type)``.
--`Line : (Point→Prop)→Prop` is a primitive relation.
-- `Line` is a ``2nd-order relation of 1-arity``.
--`L∈Line` abbreviates the propositions `Line L`.
--`L∈Line` reads `L is a line`; lines are thought of as sets of points.
--Lean has built in support for higher order logic via `Set`.
--`Set Point` is syntactic sugar for `Point→Prop`.
--`L: Set Point` means `L : Point→Prop` is a ``1st-order property``.
--Any set can be thought of as the extension of a property.
#print Set
--Sets have basic constructive principles supporting them in Lean.
open Set
--One is the usual axiom of extensionality.
example {T:Type} (S₁ S₂:Set T) : (∀x:T, x∈S₁ ↔ x∈S₂) → S₁=S₂ := ext
--`∀L∈Line, P L` abbreviates `∀L:Set Point, Line L → P L`.
--By definition, the comprehension axiom comes for free.
--I.e. for any property `P:Point→Prop`, there is a set `{p:Point ∣ P p}`.

--Sec 6. AXIOMS OF INCIDENCE
--A set of points `Point` and collection of subsets of points `Line`,
-- is an `Incidence_Geometery` iff the following axioms are satsified.
class Incidence_Geometery (Point : Type) (Line : Set (Set Point)) where
  I1 : ∀p₁ p₂:Point, p₁≠p₂ → ∃!L, Line L ∧ p₁∈L ∧ p₂∈L
  I2 : ∀L, Line L → ∃p₁ p₂:Point, p₁≠p₂ ∧ p₁∈L ∧ p₂∈L
  I3 : let Colinear (p₁ p₂ p₃:Point) : Prop := ∃!L, Line L ∧ p₁∈L ∧ p₂∈L ∧ p₃∈L
    ∃p₁ p₂ p₃:Point, ¬ Colinear p₁ p₂ p₃
--This is one approach if we wish to prove model-theoertic results,
--using Lean as the meta-theory. However we only wish to prove results
--true in all incidence geometeries. Harthsone does ask model-theoretic
--questions. However, we ignore them, drop this approach, and add axioms.

axiom Point : Type
axiom Line : Set (Set Point)
--(I1) Every pair of distint points is contained in a unique Line.
axiom I1 : ∀p₁ p₂:Point, p₁≠p₂ → ∃!L, Line L ∧ p₁∈L ∧ p₂∈L
--(I2) Every line contains two distinct points.
axiom I2 : ∀L, Line L → ∃p₁ p₂:Point, p₁≠p₂ ∧ p₁∈L ∧ p₂∈L
--(def) Three points are `Colinear` iff they all lie on the same line.
--`Colinear` is a ``1st-order property of 3-artiy``.
def Colinear (p₁ p₂ p₃:Point) : Prop := ∃L, Line L ∧ p₁∈L ∧ p₂∈L ∧ p₃∈L
--(I3) There exists three noncolinear points.
axiom I3 : ∃p₁ p₂ p₃:Point, ¬ Colinear p₁ p₂ p₃

--(6.1) Two distinct lines intersect at most on one point.
lemma Prop6_1 : ∀ᵉ(L₁∈Line)(L₂∈Line), L₁≠L₂ →
  ¬∃p₁ p₂:Point, p₁∈L₁ ∧ p₂∈L₁ ∧ p₁∈L₂ ∧ p₂∈L₂ ∧ p₁≠p₂ := by
  rintro L₁ hL₁ L₂ hL₂ hL ⟨p₁, p₂, h11, h12, h21, h22, hp⟩
  obtain ⟨L, ⟨_, _⟩, h⟩ := I1 p₁ p₂ hp; dsimp at h
  apply hL
  have := h L₁ ⟨hL₁, h11, h12⟩
  have := h L₂ ⟨by assumption, by assumption, by assumption⟩
  rw[this]; assumption

--(def) Parralell lines have either no points or all points in common.
--`Parallel` is a ``2nd-order property of 2-arity`.
def Parallel (L₁ L₂: Set Point): Prop
  := Line L₁ ∧ Line L₂ ∧ (L₁=L₂ ∨ ¬∃p:Point, p∈L₁ ∧ p∈L₂)
--(P) For each point `p` and line `L` there is at most one line
-- containing `p` parralell to `L`.
--Parallel axiom `P` that may or may not be used, and is thus defined.
--`P` is a ``0th-order property``, i.e. a proposition.
def P : Prop :=  ∀ᵉ(p:Point) (L∈Line), ¬∃L₁ L₂,
  p∈L₁ ∧ p∈L₂ ∧ Parallel L L₁ ∧ Parallel L L₂ ∧ L₁≠L₂


--Sec 6. Sud's Exercises (useful for future sections!)

--Here are alternative axiomatizations of `I2` and `I3`.
--The purpose is to make future proofs constructive.

--For every line, there exists three distinct points:
--two lie on the line, and one does not.
--Hint: suppose false; try to contraict `I3`.
--Note: this cannot be proven constructively from the axioms!
--This is why I tihnk this is a better axiom!
lemma SudI2 (l: Set Point) (_ :Line l) : ∃p₁ p₂ p₃:Point,
   p₃∉l ∧ p₂∈l ∧ p₁∈l ∧ p₁≠p₂ ∧ p₁≠p₃ ∧ p₂≠p₃ := by
  --Take any line `l`. There are two disctinct points already on the line.
  --So we must find a third not on the line.
  --Commands ``by_contra h`` and ``push_neg at h`` are useful.
  sorry

--There exists a line.
--Note: this can be proven constructively from the axioms.
lemma SudI3 : ∃l:Set Point, Line l := by
  sorry


--Sec 7. Axioms of Betweenness
--`Between : Point→Point→Point→Prop` is a primitive relation.
--`Between` is a ``1st-order relation of 3-arity``.
--`Between A B C` means `B` is between `A` and `C`.
axiom Between : Point → Point → Point → Prop
--(B1) If `A⋆B⋆C` then `A,B,C` are distinct points which
-- lie on the same line and `C⋆B⋆A`.
axiom B1 : ∀A B C:Point, Between A B C → A≠B ∧ A≠C ∧ B≠C ∧
  Between C B A ∧ ∃l:Set Point, l∈Line ∧ A∈l ∧ B∈l ∧ C∈l
--(B2) For distinct points `A,B`, there exists point `C`
-- such that `A⋆B⋆C`.
axiom B2 : ∀A B:Point, A≠B → ∃C:Point, Between A B C
--(B3) Given three distinct points on a line, one and only one of them
-- is between the other two.
axiom B3 : ∀A B C:Point, ∀l∈Line, A≠B ∧ A≠C ∧ B≠C ∧ A∈l ∧ B∈l ∧ C∈l →
   (Between A B C  ∧ ¬Between C A B ∧ ¬Between B C A) ∨
   (¬Between A B C  ∧ Between C A B ∧ ¬Between B C A) ∨
   (¬Between A B C  ∧ ¬Between C A B ∧ Between B C A)
--(B4) Let `A,B,C` be noncolinear points, none of which are contained in
-- a line `l`. If `l` contains a point `D` lying between `A,C`, then it
-- must contain a point lying either between `A,C` or `B,C` but not both.
axiom B4 (A B C:Point) (l: Set Point) (_ :Line l) (_ :¬Colinear A B C)
(_:A∉l) (_:B∉l) (_:C∉l): (∃D:Point, D∈l ∧ Between A D C) →
((∃D₁:Point, D₁∈l ∧ Between A D₁ C) ∧ (¬∃D₂:Point, D₂∈l ∧ Between B D₂ C)) ∨
((¬∃D₁:Point, D₁∈l ∧ Between A D₁ C) ∧ (∃D₂:Point, D₂∈l ∧ Between B D₂ C))

--(def) If `A,B` are distinct points then `Seg A B` is the set consisting
-- of points `A,B` and all those inbetween `A,B`.
--We define `Seg` on all points for simplicity; any result using seg will
-- usually have distinctness inferable from context.
--`Seg` is a ``2nd-order function of 2-arity`.
def Seg (A B :Point) : Set Point :=
  { P | (fun X ↦ X=A ∨ X=B ∨ Between B X A) P }
--(def) If `A,B,C` are noncolinear points, then `Tri A B C` is the union
-- of segements `A↑B, A↑C, B↑C`. Think of `Tri A B C` as the boundary
-- of a 2-simplex. Again we define `Tri` on all points and expect
-- any context involving triangles to prove noncolinearity.
--`ΔABC` denotes `Tri A B C`.
--`Tri` is a ``2nd-order function of 3-arity``.
def Tri (A B C:Point) : Set Point :=
  Seg A B ∪ Seg A C ∪ Seg B C
notation:85 "Δ" A:85 B:85 C:85 => Tri A B C
--Note: Segements `Seg A B` and `Seg B A` are equal.
lemma Note7_1 (A B:Point) : Seg A B = Seg B A := by
  unfold Seg; apply ext; intro x
  constructor
  repeat intro h; simp only [mem_setOf]; obtain (_ |_ | h3) := h;
  · right; left; assumption
  · left; assumption
  · right; right
    obtain ⟨ _, _, _ ,mark, _⟩  := B1 B x A h3
    exact mark
  · simp; rintro (_ | _ | h3);
    · right; left; assumption
    · left; assumption
    · right; right
      obtain ⟨ _, _, _ ,mark, _⟩  := B1 A x B h3
      exact mark

--(7.1) Plane separation. Let `l` be a line.
--The set of points not lying on `l` can be partitioned into two nonempty
--subsets `S₁` and `S₂` satisfying the following properties:
--(a) Points `A, B` not in `l`, belong to the same set (`S₁` or `S₂`) iff
--`Seg A B` does not intersect `l`, and
--(b) Points `A, C` not in `l` belong to the opposite sets (one in `S₁`,
--other in `S₂`) iff `Seg A C` intersects `l`.


lemma Prop7_1 (l:Set Point) (_ : Line l) : ∃ S₁ S₂ : Set Point,
  (∃x, x∈S₁) ∧ (∃x, x∈S₂) ∧ S₁∩S₂=∅ ∧ S₁∪S₂ = univ \ l ∧
  (∀ A B:Point, A∉l → B∉l →
    ((A∈S₁ ∧ B∈S₁) ∨ (A∈S₂ ∧ B∈S₂) ↔ Seg A B ∩ l = ∅))
  ∧
  (∀ A B :Point, A∉l → B∉l →
    ((A∈S₁ ∧ B∈S₂) ∨ (A∈S₂ ∧ B∈S₁) ↔ ∃x, x∈ Seg A B ∧ x∈l)) := by
--Put `R` as the relation A∼B iff A=B or `Seg A B` does not meet `l`.
let R (A B:Point) : Prop := A=B ∨ ∀ᵉ(x∈ Seg A B), x∉l
--`R` is an equivalence relation on the set of all points not lying on `l`.
--First, it is reflexive.
have R_refl : ∀ A:Point, A∉l→ R A A := by
  intro A _; dsimp; left; rfl
--Second, it is symmetric.
have R_symm : ∀ A B:Point, A∉l→B∉l→ R A B → R B A := by
  intro A B _ _ hR
  dsimp at hR ⊢
  obtain (hR | hR) := hR
  · left;  symm; exact hR
  · right
    rw [← Note7_1 A B]
    exact hR
--Third, it is transitive. To show this...
have R_trans : ∀ A B C:Point, A∉l→B∉l→C∉l→ R A B → R B C → R A C := by
  sorry

--Next, `axiom I3` (`SudI2`) implies that there are points `P₁∈l` and `A∉l`.
--So let `S₁` be the equivalence class of `A`.
obtain ⟨_, P₁, A, hA, _, _, _, _, hP1⟩ := SudI2 l (by assumption)
use {P | P∉l ∧ R A P}

--And, `axiom B2` implies there is a point `C` such that `Between A P₁ C`.
--So let `S₂` be the equivalence class of `C`.
obtain ⟨C, hC⟩ := B2 A P₁ (by exact id (Ne.symm hP1))
use {P | P∉l ∧ R P C}

--We claim `S₁` and `S₂` are the only two equivalence classes.

--First, `S₁` is nonempty since `A∼A`.
constructor
· use A; exact ⟨hA, by apply R_refl; assumption⟩

--Second, `C∉l` which implies `S₂` is nonempty since `C∼C`.
--For if `C∈l` then `Between A P₁ C` implies `A∈l`, a contradiction
have _ : C∉l := by
  intro hC
  apply hA
  obtain ⟨_, _, _, _, l₂, _, _, _, _⟩ := B1 A P₁ C (by assumption)
  obtain ⟨l₃, _, hunq⟩ := I1 P₁ C (by assumption)
  have this := hunq l ⟨by assumption, by assumption, by assumption⟩
  have that := hunq l₂ ⟨by assumption, by assumption, by assumption⟩
  rw[this, ← that]
  assumption
constructor
· use C; exact ⟨by assumption, by apply R_refl; assumption⟩

--Third. we show `S₁∩S₂=∅`.
constructor
· --We prove `B ∈ S₁∩S₂` iff `B ∈ ∅`.
  ext B
  constructor
  · -- (=>) let `B ∈ S₁∩S₂` so that `A∼B` and `B∼C`.
    rintro ⟨hB1, _, hB2, _⟩
    have hB1 : R A B := by apply hB1;
    have hB2 : R B C := hB2
    -- It suffices to show `A≁C`; that way trans gives a desired contra.
    suffices hsuff : ¬ R A C
    apply hsuff
    apply R_trans A B C
    · assumption
    · --We must show `B∉l` to apply `R_trans`.
      sorry
    · --We must actually show `C∉l` to apply `R_trans`.
      --Suppose `C∈l`. Then `Between A P₁ C` implies there is a line,
      -- say `m`, containing `A P₁ C`.
      sorry

    · assumption





    sorry

    · --Case 1: supose `A=C=P`. Since `Between A D C`,
      --the points must be distinct, a contrdiction.
      rw[← h1] at h2
      obtain ⟨_, hAC, _⟩ := B1 A D C (by assumption)
      symm at h2
      contradiction

    · --Case 2: suppose `A=P` and `Seg C P` does not meet `l`.
      rw [← h1] at h2
      --We claim `D ∈ Seg C A`; for `D` lies inbetween `A` and `C`.
      have this : D ∈ Seg C A := by
        unfold Seg
        right; right; assumption
      -- Thus the line segement connects `A` and `C` intersects `l`,
      -- namely at `D∈l`, a contradiction.
      specialize h2 D this
      contradiction

    · --Case 3: suppose `C=P` and `Seg A P` does not meet `l`.
      rw [← h2] at h1
      --We claim `D ∈ Seg A C`; for `D` lies inbetween `A` and `C`.
      have this : D ∈ Seg A C := by
        unfold Seg
        right; right;
        obtain ⟨_, _, _, _, _⟩ := B1 A D C hC
        assumption
      -- Again, the line segement connects `A` and `C` intersects `l`,
      -- namely at `D∈l`, a contradiction.
      specialize h1 D this
      contradiction

    · --Case 4: suppose `Seg A P` and `Seg C P` both do not meet `l`.

     --We claim `A P C` are not colinear points.
      have hP : ¬ Colinear A P C := by
      --Suppose they were colinear witnessed by a connecting line `l₂`.
      --Since `Between A D C`, let line `l₁` connect them together.
        intro hP
        unfold Colinear at hP
        obtain ⟨_, _, _, _, l₁, _, _, _, _⟩ := B1 _ _ _ hC
        obtain ⟨l₂, _, _, _, _⟩ := hP
        --By `I1`, there is a unique line connected `A C`.
        obtain ⟨u, ⟨_, _, _⟩, hu⟩ := I1 C A (by symm; assumption)
        dsimp at hu
        --Thus `l₁=l₂`.
        have hl1 : l₁=u := by
          apply hu
          repeat (constructor; repeat assumption)
        have hl2 : l₂=u := by
          apply hu
          repeat (constructor; repeat assumption)
        have hl12 : l₁ = l₂ := by rw [hl1]; symm; assumption

        --We claim `P≠D`.
        have _ : P≠D := by
          --Otherwise, `Between A P C` implies `D=P∈ Seg A P` and hence
          --`D∉l`, which contradicts an assumption.
          intro hD
          rw [← hD] at hC
          specialize h1 D (by rw[hD]; unfold Seg; right; left; rfl)
          contradiction

        --We claim `P≠C`.
        have _ : P≠C := by
          sorry

        --Thus `P D C` are mutually distinct points which lie on `l₁`.
        --So `B3` implies one and only one is between the others.
        have _ : P∈l₁ := by rw[hl12]; assumption
        obtain (_ | _ | _) := B3 P D C l₁
          (by assumption)
          (by constructor; assumption; constructor; assumption; constructor; assumption; constructor; assumption;  assumption)
        · sorry
        · sorry
        · sorry








      sorry


  · intro hP; contradiction

constructor
· sorry

constructor
· sorry

sorry



--We wish to call `S₁` and `S₂` the "two sides of `l`".
--Here is how we formalize this deifniton in Lean.
--For any set of points `S`, we think of  `Side S l` as the proposition
--which is true when `S` consists of points not lying on `l`,
--but lying on one "side" of `l`.
--That is,
