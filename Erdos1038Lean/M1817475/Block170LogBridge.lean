import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block170

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block170

open Set

def block170W1 : Rat := ((9117180001621217 : Rat) / 5000000000000000)
def block170W2 : Rat := (0 : Rat)
def block170W3 : Rat := ((52397606746053 : Rat) / 312500000000000)
def block170W4 : Rat := ((10121480203185391 : Rat) / 100000000000000000)
def block170S1 : Rat := ((18174751 : Rat) / 10000000)
def block170S2 : Rat := ((511587 : Rat) / 200000)
def block170S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block170S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block170V (y : ℝ) : ℝ :=
  ratPotential block170W1 block170W2 block170W3 block170W4 block170S1 block170S2 block170S3 block170S4 y

def block170LeftParamsCertificate : Bool :=
  allBoxesSameParams block170LeftBoxes block170W1 block170W2 block170W3 block170W4 block170S1 block170S2 block170S3 block170S4

theorem block170LeftParamsCertificate_eq_true :
    block170LeftParamsCertificate = true := by
  native_decide

theorem block170_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block170LeftL : ℝ) (block170LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block170S1 : ℝ))
    (hy2ne : y ≠ (block170S2 : ℝ))
    (hy3ne : y ≠ (block170S3 : ℝ))
    (hy4ne : y ≠ (block170S4 : ℝ)) :
    0 < block170V y := by
  have hcert := block170LeftCertificate_eq_true
  unfold block170LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block170LeftBoxes) (lo := block170LeftL) (hi := block170LeftR)
    (w1 := block170W1) (w2 := block170W2) (w3 := block170W3) (w4 := block170W4)
    (s1 := block170S1) (s2 := block170S2) (s3 := block170S3) (s4 := block170S4)
    hboxes hcover block170LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block170RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block170RightChunk000 block170W1 block170W2 block170W3 block170W4 block170S1 block170S2 block170S3 block170S4

theorem block170RightChunk000ParamsCertificate_eq_true :
    block170RightChunk000ParamsCertificate = true := by
  native_decide

theorem block170_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block170RightChunk000L : ℝ) (block170RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block170S1 : ℝ))
    (hy2ne : y ≠ (block170S2 : ℝ))
    (hy3ne : y ≠ (block170S3 : ℝ))
    (hy4ne : y ≠ (block170S4 : ℝ)) :
    0 < block170V y := by
  have hcert := block170RightChunk000Certificate_eq_true
  unfold block170RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block170RightChunk000) (lo := block170RightChunk000L) (hi := block170RightChunk000R)
    (w1 := block170W1) (w2 := block170W2) (w3 := block170W3) (w4 := block170W4)
    (s1 := block170S1) (s2 := block170S2) (s3 := block170S3) (s4 := block170S4)
    hboxes hcover block170RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block170RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block170RightChunk001 block170W1 block170W2 block170W3 block170W4 block170S1 block170S2 block170S3 block170S4

theorem block170RightChunk001ParamsCertificate_eq_true :
    block170RightChunk001ParamsCertificate = true := by
  native_decide

theorem block170_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block170RightChunk001L : ℝ) (block170RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block170S1 : ℝ))
    (hy2ne : y ≠ (block170S2 : ℝ))
    (hy3ne : y ≠ (block170S3 : ℝ))
    (hy4ne : y ≠ (block170S4 : ℝ)) :
    0 < block170V y := by
  have hcert := block170RightChunk001Certificate_eq_true
  unfold block170RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block170RightChunk001) (lo := block170RightChunk001L) (hi := block170RightChunk001R)
    (w1 := block170W1) (w2 := block170W2) (w3 := block170W3) (w4 := block170W4)
    (s1 := block170S1) (s2 := block170S2) (s3 := block170S3) (s4 := block170S4)
    hboxes hcover block170RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block170_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block170RightL : ℝ) (block170RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block170S1 : ℝ))
    (hy2ne : y ≠ (block170S2 : ℝ))
    (hy3ne : y ≠ (block170S3 : ℝ))
    (hy4ne : y ≠ (block170S4 : ℝ)) :
    0 < block170V y := by
  by_cases h0 : y ≤ (block170RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block170RightChunk000L : ℝ) (block170RightChunk000R : ℝ) := by
      have hL : (block170RightChunk000L : ℝ) = (block170RightL : ℝ) := by
        norm_num [block170RightChunk000L, block170RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block170_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    have hprev : (block170RightChunk000R : ℝ) < y := lt_of_not_ge h0
    have hL : (block170RightChunk001L : ℝ) = (block170RightChunk000R : ℝ) := by
      norm_num [block170RightChunk001L, block170RightChunk000R]
    have hR : (block170RightChunk001R : ℝ) = (block170RightR : ℝ) := by
      norm_num [block170RightChunk001R, block170RightR]
    have hyc : y ∈ Icc (block170RightChunk001L : ℝ) (block170RightChunk001R : ℝ) := by
      constructor
      · linarith [hprev, hL]
      · linarith [hy.2, hR]
    exact block170_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block170_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block170LeftL : ℝ) (block170LeftR : ℝ) →
    y ≠ 0 → y ≠ (block170S1 : ℝ) → y ≠ (block170S2 : ℝ) →
    y ≠ (block170S3 : ℝ) → y ≠ (block170S4 : ℝ) → 0 < block170V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block170RightL : ℝ) (block170RightR : ℝ) →
    y ≠ 0 → y ≠ (block170S1 : ℝ) → y ≠ (block170S2 : ℝ) →
    y ≠ (block170S3 : ℝ) → y ≠ (block170S4 : ℝ) → 0 < block170V y)

theorem block170_reallog_certificate_proof :
    block170_reallog_certificate := by
  exact ⟨block170_left_V_pos, block170_right_V_pos⟩

end Block170
end M1817475
end Erdos1038Lean
