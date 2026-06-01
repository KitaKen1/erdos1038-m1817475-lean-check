import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block021

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block021

open Set

def block021W1 : Rat := ((5640169407170611 : Rat) / 2500000000000000)
def block021W2 : Rat := (0 : Rat)
def block021W3 : Rat := (0 : Rat)
def block021W4 : Rat := ((578797779298997 : Rat) / 2000000000000000)
def block021S1 : Rat := ((18174751 : Rat) / 10000000)
def block021S2 : Rat := ((511587 : Rat) / 200000)
def block021S3 : Rat := ((107000619 : Rat) / 40000000)
def block021S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block021V (y : ℝ) : ℝ :=
  ratPotential block021W1 block021W2 block021W3 block021W4 block021S1 block021S2 block021S3 block021S4 y

def block021LeftParamsCertificate : Bool :=
  allBoxesSameParams block021LeftBoxes block021W1 block021W2 block021W3 block021W4 block021S1 block021S2 block021S3 block021S4

theorem block021LeftParamsCertificate_eq_true :
    block021LeftParamsCertificate = true := by
  native_decide

theorem block021_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block021LeftL : ℝ) (block021LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block021S1 : ℝ))
    (hy2ne : y ≠ (block021S2 : ℝ))
    (hy3ne : y ≠ (block021S3 : ℝ))
    (hy4ne : y ≠ (block021S4 : ℝ)) :
    0 < block021V y := by
  have hcert := block021LeftCertificate_eq_true
  unfold block021LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block021LeftBoxes) (lo := block021LeftL) (hi := block021LeftR)
    (w1 := block021W1) (w2 := block021W2) (w3 := block021W3) (w4 := block021W4)
    (s1 := block021S1) (s2 := block021S2) (s3 := block021S3) (s4 := block021S4)
    hboxes hcover block021LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block021RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block021RightChunk000 block021W1 block021W2 block021W3 block021W4 block021S1 block021S2 block021S3 block021S4

theorem block021RightChunk000ParamsCertificate_eq_true :
    block021RightChunk000ParamsCertificate = true := by
  native_decide

theorem block021_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block021RightChunk000L : ℝ) (block021RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block021S1 : ℝ))
    (hy2ne : y ≠ (block021S2 : ℝ))
    (hy3ne : y ≠ (block021S3 : ℝ))
    (hy4ne : y ≠ (block021S4 : ℝ)) :
    0 < block021V y := by
  have hcert := block021RightChunk000Certificate_eq_true
  unfold block021RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block021RightChunk000) (lo := block021RightChunk000L) (hi := block021RightChunk000R)
    (w1 := block021W1) (w2 := block021W2) (w3 := block021W3) (w4 := block021W4)
    (s1 := block021S1) (s2 := block021S2) (s3 := block021S3) (s4 := block021S4)
    hboxes hcover block021RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block021RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block021RightChunk001 block021W1 block021W2 block021W3 block021W4 block021S1 block021S2 block021S3 block021S4

theorem block021RightChunk001ParamsCertificate_eq_true :
    block021RightChunk001ParamsCertificate = true := by
  native_decide

theorem block021_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block021RightChunk001L : ℝ) (block021RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block021S1 : ℝ))
    (hy2ne : y ≠ (block021S2 : ℝ))
    (hy3ne : y ≠ (block021S3 : ℝ))
    (hy4ne : y ≠ (block021S4 : ℝ)) :
    0 < block021V y := by
  have hcert := block021RightChunk001Certificate_eq_true
  unfold block021RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block021RightChunk001) (lo := block021RightChunk001L) (hi := block021RightChunk001R)
    (w1 := block021W1) (w2 := block021W2) (w3 := block021W3) (w4 := block021W4)
    (s1 := block021S1) (s2 := block021S2) (s3 := block021S3) (s4 := block021S4)
    hboxes hcover block021RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block021_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block021RightL : ℝ) (block021RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block021S1 : ℝ))
    (hy2ne : y ≠ (block021S2 : ℝ))
    (hy3ne : y ≠ (block021S3 : ℝ))
    (hy4ne : y ≠ (block021S4 : ℝ)) :
    0 < block021V y := by
  by_cases h0 : y ≤ (block021RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block021RightChunk000L : ℝ) (block021RightChunk000R : ℝ) := by
      have hL : (block021RightChunk000L : ℝ) = (block021RightL : ℝ) := by
        norm_num [block021RightChunk000L, block021RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block021_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    have hprev : (block021RightChunk000R : ℝ) < y := lt_of_not_ge h0
    have hL : (block021RightChunk001L : ℝ) = (block021RightChunk000R : ℝ) := by
      norm_num [block021RightChunk001L, block021RightChunk000R]
    have hR : (block021RightChunk001R : ℝ) = (block021RightR : ℝ) := by
      norm_num [block021RightChunk001R, block021RightR]
    have hyc : y ∈ Icc (block021RightChunk001L : ℝ) (block021RightChunk001R : ℝ) := by
      constructor
      · linarith [hprev, hL]
      · linarith [hy.2, hR]
    exact block021_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block021_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block021LeftL : ℝ) (block021LeftR : ℝ) →
    y ≠ 0 → y ≠ (block021S1 : ℝ) → y ≠ (block021S2 : ℝ) →
    y ≠ (block021S3 : ℝ) → y ≠ (block021S4 : ℝ) → 0 < block021V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block021RightL : ℝ) (block021RightR : ℝ) →
    y ≠ 0 → y ≠ (block021S1 : ℝ) → y ≠ (block021S2 : ℝ) →
    y ≠ (block021S3 : ℝ) → y ≠ (block021S4 : ℝ) → 0 < block021V y)

theorem block021_reallog_certificate_proof :
    block021_reallog_certificate := by
  exact ⟨block021_left_V_pos, block021_right_V_pos⟩

end Block021
end M1817475
end Erdos1038Lean
