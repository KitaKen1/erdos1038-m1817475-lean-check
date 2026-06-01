import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block171

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block171

open Set

def block171W1 : Rat := ((113774152801223 : Rat) / 62500000000000)
def block171W2 : Rat := (0 : Rat)
def block171W3 : Rat := ((2101962447137189 : Rat) / 12500000000000000)
def block171W4 : Rat := ((10086329484976389 : Rat) / 100000000000000000)
def block171S1 : Rat := ((18174751 : Rat) / 10000000)
def block171S2 : Rat := ((511587 : Rat) / 200000)
def block171S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block171S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block171V (y : ℝ) : ℝ :=
  ratPotential block171W1 block171W2 block171W3 block171W4 block171S1 block171S2 block171S3 block171S4 y

def block171LeftParamsCertificate : Bool :=
  allBoxesSameParams block171LeftBoxes block171W1 block171W2 block171W3 block171W4 block171S1 block171S2 block171S3 block171S4

theorem block171LeftParamsCertificate_eq_true :
    block171LeftParamsCertificate = true := by
  native_decide

theorem block171_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block171LeftL : ℝ) (block171LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block171S1 : ℝ))
    (hy2ne : y ≠ (block171S2 : ℝ))
    (hy3ne : y ≠ (block171S3 : ℝ))
    (hy4ne : y ≠ (block171S4 : ℝ)) :
    0 < block171V y := by
  have hcert := block171LeftCertificate_eq_true
  unfold block171LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block171LeftBoxes) (lo := block171LeftL) (hi := block171LeftR)
    (w1 := block171W1) (w2 := block171W2) (w3 := block171W3) (w4 := block171W4)
    (s1 := block171S1) (s2 := block171S2) (s3 := block171S3) (s4 := block171S4)
    hboxes hcover block171LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block171RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block171RightChunk000 block171W1 block171W2 block171W3 block171W4 block171S1 block171S2 block171S3 block171S4

theorem block171RightChunk000ParamsCertificate_eq_true :
    block171RightChunk000ParamsCertificate = true := by
  native_decide

theorem block171_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block171RightChunk000L : ℝ) (block171RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block171S1 : ℝ))
    (hy2ne : y ≠ (block171S2 : ℝ))
    (hy3ne : y ≠ (block171S3 : ℝ))
    (hy4ne : y ≠ (block171S4 : ℝ)) :
    0 < block171V y := by
  have hcert := block171RightChunk000Certificate_eq_true
  unfold block171RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block171RightChunk000) (lo := block171RightChunk000L) (hi := block171RightChunk000R)
    (w1 := block171W1) (w2 := block171W2) (w3 := block171W3) (w4 := block171W4)
    (s1 := block171S1) (s2 := block171S2) (s3 := block171S3) (s4 := block171S4)
    hboxes hcover block171RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block171RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block171RightChunk001 block171W1 block171W2 block171W3 block171W4 block171S1 block171S2 block171S3 block171S4

theorem block171RightChunk001ParamsCertificate_eq_true :
    block171RightChunk001ParamsCertificate = true := by
  native_decide

theorem block171_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block171RightChunk001L : ℝ) (block171RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block171S1 : ℝ))
    (hy2ne : y ≠ (block171S2 : ℝ))
    (hy3ne : y ≠ (block171S3 : ℝ))
    (hy4ne : y ≠ (block171S4 : ℝ)) :
    0 < block171V y := by
  have hcert := block171RightChunk001Certificate_eq_true
  unfold block171RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block171RightChunk001) (lo := block171RightChunk001L) (hi := block171RightChunk001R)
    (w1 := block171W1) (w2 := block171W2) (w3 := block171W3) (w4 := block171W4)
    (s1 := block171S1) (s2 := block171S2) (s3 := block171S3) (s4 := block171S4)
    hboxes hcover block171RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block171_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block171RightL : ℝ) (block171RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block171S1 : ℝ))
    (hy2ne : y ≠ (block171S2 : ℝ))
    (hy3ne : y ≠ (block171S3 : ℝ))
    (hy4ne : y ≠ (block171S4 : ℝ)) :
    0 < block171V y := by
  by_cases h0 : y ≤ (block171RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block171RightChunk000L : ℝ) (block171RightChunk000R : ℝ) := by
      have hL : (block171RightChunk000L : ℝ) = (block171RightL : ℝ) := by
        norm_num [block171RightChunk000L, block171RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block171_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    have hprev : (block171RightChunk000R : ℝ) < y := lt_of_not_ge h0
    have hL : (block171RightChunk001L : ℝ) = (block171RightChunk000R : ℝ) := by
      norm_num [block171RightChunk001L, block171RightChunk000R]
    have hR : (block171RightChunk001R : ℝ) = (block171RightR : ℝ) := by
      norm_num [block171RightChunk001R, block171RightR]
    have hyc : y ∈ Icc (block171RightChunk001L : ℝ) (block171RightChunk001R : ℝ) := by
      constructor
      · linarith [hprev, hL]
      · linarith [hy.2, hR]
    exact block171_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block171_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block171LeftL : ℝ) (block171LeftR : ℝ) →
    y ≠ 0 → y ≠ (block171S1 : ℝ) → y ≠ (block171S2 : ℝ) →
    y ≠ (block171S3 : ℝ) → y ≠ (block171S4 : ℝ) → 0 < block171V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block171RightL : ℝ) (block171RightR : ℝ) →
    y ≠ 0 → y ≠ (block171S1 : ℝ) → y ≠ (block171S2 : ℝ) →
    y ≠ (block171S3 : ℝ) → y ≠ (block171S4 : ℝ) → 0 < block171V y)

theorem block171_reallog_certificate_proof :
    block171_reallog_certificate := by
  exact ⟨block171_left_V_pos, block171_right_V_pos⟩

end Block171
end M1817475
end Erdos1038Lean
