import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block181

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block181

open Set

def block181W1 : Rat := ((1783617053519739 : Rat) / 1000000000000000)
def block181W2 : Rat := (0 : Rat)
def block181W3 : Rat := ((8709504852769201 : Rat) / 50000000000000000)
def block181W4 : Rat := ((4828890932775437 : Rat) / 50000000000000000)
def block181S1 : Rat := ((18174751 : Rat) / 10000000)
def block181S2 : Rat := ((511587 : Rat) / 200000)
def block181S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block181S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block181V (y : ℝ) : ℝ :=
  ratPotential block181W1 block181W2 block181W3 block181W4 block181S1 block181S2 block181S3 block181S4 y

def block181LeftParamsCertificate : Bool :=
  allBoxesSameParams block181LeftBoxes block181W1 block181W2 block181W3 block181W4 block181S1 block181S2 block181S3 block181S4

theorem block181LeftParamsCertificate_eq_true :
    block181LeftParamsCertificate = true := by
  native_decide

theorem block181_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block181LeftL : ℝ) (block181LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block181S1 : ℝ))
    (hy2ne : y ≠ (block181S2 : ℝ))
    (hy3ne : y ≠ (block181S3 : ℝ))
    (hy4ne : y ≠ (block181S4 : ℝ)) :
    0 < block181V y := by
  have hcert := block181LeftCertificate_eq_true
  unfold block181LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block181LeftBoxes) (lo := block181LeftL) (hi := block181LeftR)
    (w1 := block181W1) (w2 := block181W2) (w3 := block181W3) (w4 := block181W4)
    (s1 := block181S1) (s2 := block181S2) (s3 := block181S3) (s4 := block181S4)
    hboxes hcover block181LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block181RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block181RightChunk000 block181W1 block181W2 block181W3 block181W4 block181S1 block181S2 block181S3 block181S4

theorem block181RightChunk000ParamsCertificate_eq_true :
    block181RightChunk000ParamsCertificate = true := by
  native_decide

theorem block181_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block181RightChunk000L : ℝ) (block181RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block181S1 : ℝ))
    (hy2ne : y ≠ (block181S2 : ℝ))
    (hy3ne : y ≠ (block181S3 : ℝ))
    (hy4ne : y ≠ (block181S4 : ℝ)) :
    0 < block181V y := by
  have hcert := block181RightChunk000Certificate_eq_true
  unfold block181RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block181RightChunk000) (lo := block181RightChunk000L) (hi := block181RightChunk000R)
    (w1 := block181W1) (w2 := block181W2) (w3 := block181W3) (w4 := block181W4)
    (s1 := block181S1) (s2 := block181S2) (s3 := block181S3) (s4 := block181S4)
    hboxes hcover block181RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block181RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block181RightChunk001 block181W1 block181W2 block181W3 block181W4 block181S1 block181S2 block181S3 block181S4

theorem block181RightChunk001ParamsCertificate_eq_true :
    block181RightChunk001ParamsCertificate = true := by
  native_decide

theorem block181_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block181RightChunk001L : ℝ) (block181RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block181S1 : ℝ))
    (hy2ne : y ≠ (block181S2 : ℝ))
    (hy3ne : y ≠ (block181S3 : ℝ))
    (hy4ne : y ≠ (block181S4 : ℝ)) :
    0 < block181V y := by
  have hcert := block181RightChunk001Certificate_eq_true
  unfold block181RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block181RightChunk001) (lo := block181RightChunk001L) (hi := block181RightChunk001R)
    (w1 := block181W1) (w2 := block181W2) (w3 := block181W3) (w4 := block181W4)
    (s1 := block181S1) (s2 := block181S2) (s3 := block181S3) (s4 := block181S4)
    hboxes hcover block181RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block181_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block181RightL : ℝ) (block181RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block181S1 : ℝ))
    (hy2ne : y ≠ (block181S2 : ℝ))
    (hy3ne : y ≠ (block181S3 : ℝ))
    (hy4ne : y ≠ (block181S4 : ℝ)) :
    0 < block181V y := by
  by_cases h0 : y ≤ (block181RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block181RightChunk000L : ℝ) (block181RightChunk000R : ℝ) := by
      have hL : (block181RightChunk000L : ℝ) = (block181RightL : ℝ) := by
        norm_num [block181RightChunk000L, block181RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block181_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    have hprev : (block181RightChunk000R : ℝ) < y := lt_of_not_ge h0
    have hL : (block181RightChunk001L : ℝ) = (block181RightChunk000R : ℝ) := by
      norm_num [block181RightChunk001L, block181RightChunk000R]
    have hR : (block181RightChunk001R : ℝ) = (block181RightR : ℝ) := by
      norm_num [block181RightChunk001R, block181RightR]
    have hyc : y ∈ Icc (block181RightChunk001L : ℝ) (block181RightChunk001R : ℝ) := by
      constructor
      · linarith [hprev, hL]
      · linarith [hy.2, hR]
    exact block181_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block181_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block181LeftL : ℝ) (block181LeftR : ℝ) →
    y ≠ 0 → y ≠ (block181S1 : ℝ) → y ≠ (block181S2 : ℝ) →
    y ≠ (block181S3 : ℝ) → y ≠ (block181S4 : ℝ) → 0 < block181V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block181RightL : ℝ) (block181RightR : ℝ) →
    y ≠ 0 → y ≠ (block181S1 : ℝ) → y ≠ (block181S2 : ℝ) →
    y ≠ (block181S3 : ℝ) → y ≠ (block181S4 : ℝ) → 0 < block181V y)

theorem block181_reallog_certificate_proof :
    block181_reallog_certificate := by
  exact ⟨block181_left_V_pos, block181_right_V_pos⟩

end Block181
end M1817475
end Erdos1038Lean
