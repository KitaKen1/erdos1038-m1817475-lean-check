import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block182

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block182

open Set

def block182W1 : Rat := ((4448983245285567 : Rat) / 2500000000000000)
def block182W2 : Rat := (0 : Rat)
def block182W3 : Rat := ((1748643225436041 : Rat) / 10000000000000000)
def block182W4 : Rat := ((4805280893421233 : Rat) / 50000000000000000)
def block182S1 : Rat := ((18174751 : Rat) / 10000000)
def block182S2 : Rat := ((511587 : Rat) / 200000)
def block182S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block182S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block182V (y : ℝ) : ℝ :=
  ratPotential block182W1 block182W2 block182W3 block182W4 block182S1 block182S2 block182S3 block182S4 y

def block182LeftParamsCertificate : Bool :=
  allBoxesSameParams block182LeftBoxes block182W1 block182W2 block182W3 block182W4 block182S1 block182S2 block182S3 block182S4

theorem block182LeftParamsCertificate_eq_true :
    block182LeftParamsCertificate = true := by
  native_decide

theorem block182_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block182LeftL : ℝ) (block182LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block182S1 : ℝ))
    (hy2ne : y ≠ (block182S2 : ℝ))
    (hy3ne : y ≠ (block182S3 : ℝ))
    (hy4ne : y ≠ (block182S4 : ℝ)) :
    0 < block182V y := by
  have hcert := block182LeftCertificate_eq_true
  unfold block182LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block182LeftBoxes) (lo := block182LeftL) (hi := block182LeftR)
    (w1 := block182W1) (w2 := block182W2) (w3 := block182W3) (w4 := block182W4)
    (s1 := block182S1) (s2 := block182S2) (s3 := block182S3) (s4 := block182S4)
    hboxes hcover block182LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block182RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block182RightChunk000 block182W1 block182W2 block182W3 block182W4 block182S1 block182S2 block182S3 block182S4

theorem block182RightChunk000ParamsCertificate_eq_true :
    block182RightChunk000ParamsCertificate = true := by
  native_decide

theorem block182_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block182RightChunk000L : ℝ) (block182RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block182S1 : ℝ))
    (hy2ne : y ≠ (block182S2 : ℝ))
    (hy3ne : y ≠ (block182S3 : ℝ))
    (hy4ne : y ≠ (block182S4 : ℝ)) :
    0 < block182V y := by
  have hcert := block182RightChunk000Certificate_eq_true
  unfold block182RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block182RightChunk000) (lo := block182RightChunk000L) (hi := block182RightChunk000R)
    (w1 := block182W1) (w2 := block182W2) (w3 := block182W3) (w4 := block182W4)
    (s1 := block182S1) (s2 := block182S2) (s3 := block182S3) (s4 := block182S4)
    hboxes hcover block182RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block182RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block182RightChunk001 block182W1 block182W2 block182W3 block182W4 block182S1 block182S2 block182S3 block182S4

theorem block182RightChunk001ParamsCertificate_eq_true :
    block182RightChunk001ParamsCertificate = true := by
  native_decide

theorem block182_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block182RightChunk001L : ℝ) (block182RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block182S1 : ℝ))
    (hy2ne : y ≠ (block182S2 : ℝ))
    (hy3ne : y ≠ (block182S3 : ℝ))
    (hy4ne : y ≠ (block182S4 : ℝ)) :
    0 < block182V y := by
  have hcert := block182RightChunk001Certificate_eq_true
  unfold block182RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block182RightChunk001) (lo := block182RightChunk001L) (hi := block182RightChunk001R)
    (w1 := block182W1) (w2 := block182W2) (w3 := block182W3) (w4 := block182W4)
    (s1 := block182S1) (s2 := block182S2) (s3 := block182S3) (s4 := block182S4)
    hboxes hcover block182RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block182_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block182RightL : ℝ) (block182RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block182S1 : ℝ))
    (hy2ne : y ≠ (block182S2 : ℝ))
    (hy3ne : y ≠ (block182S3 : ℝ))
    (hy4ne : y ≠ (block182S4 : ℝ)) :
    0 < block182V y := by
  by_cases h0 : y ≤ (block182RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block182RightChunk000L : ℝ) (block182RightChunk000R : ℝ) := by
      have hL : (block182RightChunk000L : ℝ) = (block182RightL : ℝ) := by
        norm_num [block182RightChunk000L, block182RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block182_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    have hprev : (block182RightChunk000R : ℝ) < y := lt_of_not_ge h0
    have hL : (block182RightChunk001L : ℝ) = (block182RightChunk000R : ℝ) := by
      norm_num [block182RightChunk001L, block182RightChunk000R]
    have hR : (block182RightChunk001R : ℝ) = (block182RightR : ℝ) := by
      norm_num [block182RightChunk001R, block182RightR]
    have hyc : y ∈ Icc (block182RightChunk001L : ℝ) (block182RightChunk001R : ℝ) := by
      constructor
      · linarith [hprev, hL]
      · linarith [hy.2, hR]
    exact block182_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block182_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block182LeftL : ℝ) (block182LeftR : ℝ) →
    y ≠ 0 → y ≠ (block182S1 : ℝ) → y ≠ (block182S2 : ℝ) →
    y ≠ (block182S3 : ℝ) → y ≠ (block182S4 : ℝ) → 0 < block182V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block182RightL : ℝ) (block182RightR : ℝ) →
    y ≠ 0 → y ≠ (block182S1 : ℝ) → y ≠ (block182S2 : ℝ) →
    y ≠ (block182S3 : ℝ) → y ≠ (block182S4 : ℝ) → 0 < block182V y)

theorem block182_reallog_certificate_proof :
    block182_reallog_certificate := by
  exact ⟨block182_left_V_pos, block182_right_V_pos⟩

end Block182
end M1817475
end Erdos1038Lean
