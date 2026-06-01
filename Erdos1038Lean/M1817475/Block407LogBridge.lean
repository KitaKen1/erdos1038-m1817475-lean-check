import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block407

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block407

open Set

def block407W1 : Rat := ((291286471583419 : Rat) / 400000000000000)
def block407W2 : Rat := (0 : Rat)
def block407W3 : Rat := ((5661722292537289 : Rat) / 20000000000000000)
def block407W4 : Rat := ((9099907830316023 : Rat) / 100000000000000000)
def block407S1 : Rat := ((18174751 : Rat) / 10000000)
def block407S2 : Rat := ((511587 : Rat) / 200000)
def block407S3 : Rat := ((132177070625000000069 : Rat) / 50000000000000000000)
def block407S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block407V (y : ℝ) : ℝ :=
  ratPotential block407W1 block407W2 block407W3 block407W4 block407S1 block407S2 block407S3 block407S4 y

def block407LeftParamsCertificate : Bool :=
  allBoxesSameParams block407LeftBoxes block407W1 block407W2 block407W3 block407W4 block407S1 block407S2 block407S3 block407S4

theorem block407LeftParamsCertificate_eq_true :
    block407LeftParamsCertificate = true := by
  native_decide

theorem block407_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block407LeftL : ℝ) (block407LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block407S1 : ℝ))
    (hy2ne : y ≠ (block407S2 : ℝ))
    (hy3ne : y ≠ (block407S3 : ℝ))
    (hy4ne : y ≠ (block407S4 : ℝ)) :
    0 < block407V y := by
  have hcert := block407LeftCertificate_eq_true
  unfold block407LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block407LeftBoxes) (lo := block407LeftL) (hi := block407LeftR)
    (w1 := block407W1) (w2 := block407W2) (w3 := block407W3) (w4 := block407W4)
    (s1 := block407S1) (s2 := block407S2) (s3 := block407S3) (s4 := block407S4)
    hboxes hcover block407LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block407RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block407RightChunk000 block407W1 block407W2 block407W3 block407W4 block407S1 block407S2 block407S3 block407S4

theorem block407RightChunk000ParamsCertificate_eq_true :
    block407RightChunk000ParamsCertificate = true := by
  native_decide

theorem block407_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block407RightChunk000L : ℝ) (block407RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block407S1 : ℝ))
    (hy2ne : y ≠ (block407S2 : ℝ))
    (hy3ne : y ≠ (block407S3 : ℝ))
    (hy4ne : y ≠ (block407S4 : ℝ)) :
    0 < block407V y := by
  have hcert := block407RightChunk000Certificate_eq_true
  unfold block407RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block407RightChunk000) (lo := block407RightChunk000L) (hi := block407RightChunk000R)
    (w1 := block407W1) (w2 := block407W2) (w3 := block407W3) (w4 := block407W4)
    (s1 := block407S1) (s2 := block407S2) (s3 := block407S3) (s4 := block407S4)
    hboxes hcover block407RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block407RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block407RightChunk001 block407W1 block407W2 block407W3 block407W4 block407S1 block407S2 block407S3 block407S4

theorem block407RightChunk001ParamsCertificate_eq_true :
    block407RightChunk001ParamsCertificate = true := by
  native_decide

theorem block407_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block407RightChunk001L : ℝ) (block407RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block407S1 : ℝ))
    (hy2ne : y ≠ (block407S2 : ℝ))
    (hy3ne : y ≠ (block407S3 : ℝ))
    (hy4ne : y ≠ (block407S4 : ℝ)) :
    0 < block407V y := by
  have hcert := block407RightChunk001Certificate_eq_true
  unfold block407RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block407RightChunk001) (lo := block407RightChunk001L) (hi := block407RightChunk001R)
    (w1 := block407W1) (w2 := block407W2) (w3 := block407W3) (w4 := block407W4)
    (s1 := block407S1) (s2 := block407S2) (s3 := block407S3) (s4 := block407S4)
    hboxes hcover block407RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block407_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block407RightL : ℝ) (block407RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block407S1 : ℝ))
    (hy2ne : y ≠ (block407S2 : ℝ))
    (hy3ne : y ≠ (block407S3 : ℝ))
    (hy4ne : y ≠ (block407S4 : ℝ)) :
    0 < block407V y := by
  by_cases h0 : y ≤ (block407RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block407RightChunk000L : ℝ) (block407RightChunk000R : ℝ) := by
      have hL : (block407RightChunk000L : ℝ) = (block407RightL : ℝ) := by
        norm_num [block407RightChunk000L, block407RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block407_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    have hprev : (block407RightChunk000R : ℝ) < y := lt_of_not_ge h0
    have hL : (block407RightChunk001L : ℝ) = (block407RightChunk000R : ℝ) := by
      norm_num [block407RightChunk001L, block407RightChunk000R]
    have hR : (block407RightChunk001R : ℝ) = (block407RightR : ℝ) := by
      norm_num [block407RightChunk001R, block407RightR]
    have hyc : y ∈ Icc (block407RightChunk001L : ℝ) (block407RightChunk001R : ℝ) := by
      constructor
      · linarith [hprev, hL]
      · linarith [hy.2, hR]
    exact block407_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block407_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block407LeftL : ℝ) (block407LeftR : ℝ) →
    y ≠ 0 → y ≠ (block407S1 : ℝ) → y ≠ (block407S2 : ℝ) →
    y ≠ (block407S3 : ℝ) → y ≠ (block407S4 : ℝ) → 0 < block407V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block407RightL : ℝ) (block407RightR : ℝ) →
    y ≠ 0 → y ≠ (block407S1 : ℝ) → y ≠ (block407S2 : ℝ) →
    y ≠ (block407S3 : ℝ) → y ≠ (block407S4 : ℝ) → 0 < block407V y)

theorem block407_reallog_certificate_proof :
    block407_reallog_certificate := by
  exact ⟨block407_left_V_pos, block407_right_V_pos⟩

end Block407
end M1817475
end Erdos1038Lean
