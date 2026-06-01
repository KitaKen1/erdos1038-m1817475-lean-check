import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block175

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block175

open Set

def block175W1 : Rat := ((9024418735705181 : Rat) / 5000000000000000)
def block175W2 : Rat := (0 : Rat)
def block175W3 : Rat := ((17069263745454563 : Rat) / 100000000000000000)
def block175W4 : Rat := ((9905721773257943 : Rat) / 100000000000000000)
def block175S1 : Rat := ((18174751 : Rat) / 10000000)
def block175S2 : Rat := ((511587 : Rat) / 200000)
def block175S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block175S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block175V (y : ℝ) : ℝ :=
  ratPotential block175W1 block175W2 block175W3 block175W4 block175S1 block175S2 block175S3 block175S4 y

def block175LeftParamsCertificate : Bool :=
  allBoxesSameParams block175LeftBoxes block175W1 block175W2 block175W3 block175W4 block175S1 block175S2 block175S3 block175S4

theorem block175LeftParamsCertificate_eq_true :
    block175LeftParamsCertificate = true := by
  native_decide

theorem block175_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block175LeftL : ℝ) (block175LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block175S1 : ℝ))
    (hy2ne : y ≠ (block175S2 : ℝ))
    (hy3ne : y ≠ (block175S3 : ℝ))
    (hy4ne : y ≠ (block175S4 : ℝ)) :
    0 < block175V y := by
  have hcert := block175LeftCertificate_eq_true
  unfold block175LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block175LeftBoxes) (lo := block175LeftL) (hi := block175LeftR)
    (w1 := block175W1) (w2 := block175W2) (w3 := block175W3) (w4 := block175W4)
    (s1 := block175S1) (s2 := block175S2) (s3 := block175S3) (s4 := block175S4)
    hboxes hcover block175LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block175RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block175RightChunk000 block175W1 block175W2 block175W3 block175W4 block175S1 block175S2 block175S3 block175S4

theorem block175RightChunk000ParamsCertificate_eq_true :
    block175RightChunk000ParamsCertificate = true := by
  native_decide

theorem block175_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block175RightChunk000L : ℝ) (block175RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block175S1 : ℝ))
    (hy2ne : y ≠ (block175S2 : ℝ))
    (hy3ne : y ≠ (block175S3 : ℝ))
    (hy4ne : y ≠ (block175S4 : ℝ)) :
    0 < block175V y := by
  have hcert := block175RightChunk000Certificate_eq_true
  unfold block175RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block175RightChunk000) (lo := block175RightChunk000L) (hi := block175RightChunk000R)
    (w1 := block175W1) (w2 := block175W2) (w3 := block175W3) (w4 := block175W4)
    (s1 := block175S1) (s2 := block175S2) (s3 := block175S3) (s4 := block175S4)
    hboxes hcover block175RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block175RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block175RightChunk001 block175W1 block175W2 block175W3 block175W4 block175S1 block175S2 block175S3 block175S4

theorem block175RightChunk001ParamsCertificate_eq_true :
    block175RightChunk001ParamsCertificate = true := by
  native_decide

theorem block175_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block175RightChunk001L : ℝ) (block175RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block175S1 : ℝ))
    (hy2ne : y ≠ (block175S2 : ℝ))
    (hy3ne : y ≠ (block175S3 : ℝ))
    (hy4ne : y ≠ (block175S4 : ℝ)) :
    0 < block175V y := by
  have hcert := block175RightChunk001Certificate_eq_true
  unfold block175RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block175RightChunk001) (lo := block175RightChunk001L) (hi := block175RightChunk001R)
    (w1 := block175W1) (w2 := block175W2) (w3 := block175W3) (w4 := block175W4)
    (s1 := block175S1) (s2 := block175S2) (s3 := block175S3) (s4 := block175S4)
    hboxes hcover block175RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block175_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block175RightL : ℝ) (block175RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block175S1 : ℝ))
    (hy2ne : y ≠ (block175S2 : ℝ))
    (hy3ne : y ≠ (block175S3 : ℝ))
    (hy4ne : y ≠ (block175S4 : ℝ)) :
    0 < block175V y := by
  by_cases h0 : y ≤ (block175RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block175RightChunk000L : ℝ) (block175RightChunk000R : ℝ) := by
      have hL : (block175RightChunk000L : ℝ) = (block175RightL : ℝ) := by
        norm_num [block175RightChunk000L, block175RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block175_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    have hprev : (block175RightChunk000R : ℝ) < y := lt_of_not_ge h0
    have hL : (block175RightChunk001L : ℝ) = (block175RightChunk000R : ℝ) := by
      norm_num [block175RightChunk001L, block175RightChunk000R]
    have hR : (block175RightChunk001R : ℝ) = (block175RightR : ℝ) := by
      norm_num [block175RightChunk001R, block175RightR]
    have hyc : y ∈ Icc (block175RightChunk001L : ℝ) (block175RightChunk001R : ℝ) := by
      constructor
      · linarith [hprev, hL]
      · linarith [hy.2, hR]
    exact block175_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block175_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block175LeftL : ℝ) (block175LeftR : ℝ) →
    y ≠ 0 → y ≠ (block175S1 : ℝ) → y ≠ (block175S2 : ℝ) →
    y ≠ (block175S3 : ℝ) → y ≠ (block175S4 : ℝ) → 0 < block175V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block175RightL : ℝ) (block175RightR : ℝ) →
    y ≠ 0 → y ≠ (block175S1 : ℝ) → y ≠ (block175S2 : ℝ) →
    y ≠ (block175S3 : ℝ) → y ≠ (block175S4 : ℝ) → 0 < block175V y)

theorem block175_reallog_certificate_proof :
    block175_reallog_certificate := by
  exact ⟨block175_left_V_pos, block175_right_V_pos⟩

end Block175
end M1817475
end Erdos1038Lean
