import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block023

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block023

open Set

def block023W1 : Rat := ((456169689131047 : Rat) / 200000000000000)
def block023W2 : Rat := (0 : Rat)
def block023W3 : Rat := (0 : Rat)
def block023W4 : Rat := ((2880649889557893 : Rat) / 10000000000000000)
def block023S1 : Rat := ((18174751 : Rat) / 10000000)
def block023S2 : Rat := ((511587 : Rat) / 200000)
def block023S3 : Rat := ((107000619 : Rat) / 40000000)
def block023S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block023V (y : ℝ) : ℝ :=
  ratPotential block023W1 block023W2 block023W3 block023W4 block023S1 block023S2 block023S3 block023S4 y

def block023LeftParamsCertificate : Bool :=
  allBoxesSameParams block023LeftBoxes block023W1 block023W2 block023W3 block023W4 block023S1 block023S2 block023S3 block023S4

theorem block023LeftParamsCertificate_eq_true :
    block023LeftParamsCertificate = true := by
  native_decide

theorem block023_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block023LeftL : ℝ) (block023LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block023S1 : ℝ))
    (hy2ne : y ≠ (block023S2 : ℝ))
    (hy3ne : y ≠ (block023S3 : ℝ))
    (hy4ne : y ≠ (block023S4 : ℝ)) :
    0 < block023V y := by
  have hcert := block023LeftCertificate_eq_true
  unfold block023LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block023LeftBoxes) (lo := block023LeftL) (hi := block023LeftR)
    (w1 := block023W1) (w2 := block023W2) (w3 := block023W3) (w4 := block023W4)
    (s1 := block023S1) (s2 := block023S2) (s3 := block023S3) (s4 := block023S4)
    hboxes hcover block023LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block023RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block023RightChunk000 block023W1 block023W2 block023W3 block023W4 block023S1 block023S2 block023S3 block023S4

theorem block023RightChunk000ParamsCertificate_eq_true :
    block023RightChunk000ParamsCertificate = true := by
  native_decide

theorem block023_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block023RightChunk000L : ℝ) (block023RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block023S1 : ℝ))
    (hy2ne : y ≠ (block023S2 : ℝ))
    (hy3ne : y ≠ (block023S3 : ℝ))
    (hy4ne : y ≠ (block023S4 : ℝ)) :
    0 < block023V y := by
  have hcert := block023RightChunk000Certificate_eq_true
  unfold block023RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block023RightChunk000) (lo := block023RightChunk000L) (hi := block023RightChunk000R)
    (w1 := block023W1) (w2 := block023W2) (w3 := block023W3) (w4 := block023W4)
    (s1 := block023S1) (s2 := block023S2) (s3 := block023S3) (s4 := block023S4)
    hboxes hcover block023RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block023RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block023RightChunk001 block023W1 block023W2 block023W3 block023W4 block023S1 block023S2 block023S3 block023S4

theorem block023RightChunk001ParamsCertificate_eq_true :
    block023RightChunk001ParamsCertificate = true := by
  native_decide

theorem block023_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block023RightChunk001L : ℝ) (block023RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block023S1 : ℝ))
    (hy2ne : y ≠ (block023S2 : ℝ))
    (hy3ne : y ≠ (block023S3 : ℝ))
    (hy4ne : y ≠ (block023S4 : ℝ)) :
    0 < block023V y := by
  have hcert := block023RightChunk001Certificate_eq_true
  unfold block023RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block023RightChunk001) (lo := block023RightChunk001L) (hi := block023RightChunk001R)
    (w1 := block023W1) (w2 := block023W2) (w3 := block023W3) (w4 := block023W4)
    (s1 := block023S1) (s2 := block023S2) (s3 := block023S3) (s4 := block023S4)
    hboxes hcover block023RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block023_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block023RightL : ℝ) (block023RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block023S1 : ℝ))
    (hy2ne : y ≠ (block023S2 : ℝ))
    (hy3ne : y ≠ (block023S3 : ℝ))
    (hy4ne : y ≠ (block023S4 : ℝ)) :
    0 < block023V y := by
  by_cases h0 : y ≤ (block023RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block023RightChunk000L : ℝ) (block023RightChunk000R : ℝ) := by
      have hL : (block023RightChunk000L : ℝ) = (block023RightL : ℝ) := by
        norm_num [block023RightChunk000L, block023RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block023_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    have hprev : (block023RightChunk000R : ℝ) < y := lt_of_not_ge h0
    have hL : (block023RightChunk001L : ℝ) = (block023RightChunk000R : ℝ) := by
      norm_num [block023RightChunk001L, block023RightChunk000R]
    have hR : (block023RightChunk001R : ℝ) = (block023RightR : ℝ) := by
      norm_num [block023RightChunk001R, block023RightR]
    have hyc : y ∈ Icc (block023RightChunk001L : ℝ) (block023RightChunk001R : ℝ) := by
      constructor
      · linarith [hprev, hL]
      · linarith [hy.2, hR]
    exact block023_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block023_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block023LeftL : ℝ) (block023LeftR : ℝ) →
    y ≠ 0 → y ≠ (block023S1 : ℝ) → y ≠ (block023S2 : ℝ) →
    y ≠ (block023S3 : ℝ) → y ≠ (block023S4 : ℝ) → 0 < block023V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block023RightL : ℝ) (block023RightR : ℝ) →
    y ≠ 0 → y ≠ (block023S1 : ℝ) → y ≠ (block023S2 : ℝ) →
    y ≠ (block023S3 : ℝ) → y ≠ (block023S4 : ℝ) → 0 < block023V y)

theorem block023_reallog_certificate_proof :
    block023_reallog_certificate := by
  exact ⟨block023_left_V_pos, block023_right_V_pos⟩

end Block023
end M1817475
end Erdos1038Lean
