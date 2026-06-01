import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block419

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block419

open Set

def block419W1 : Rat := ((862075096149699 : Rat) / 1250000000000000)
def block419W2 : Rat := (0 : Rat)
def block419W3 : Rat := ((591657806942913 : Rat) / 2000000000000000)
def block419W4 : Rat := ((1066925663140523 : Rat) / 12500000000000000)
def block419S1 : Rat := ((18174751 : Rat) / 10000000)
def block419S2 : Rat := ((511587 : Rat) / 200000)
def block419S3 : Rat := ((26388496267857142873 : Rat) / 10000000000000000000)
def block419S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block419V (y : ℝ) : ℝ :=
  ratPotential block419W1 block419W2 block419W3 block419W4 block419S1 block419S2 block419S3 block419S4 y

def block419LeftParamsCertificate : Bool :=
  allBoxesSameParams block419LeftBoxes block419W1 block419W2 block419W3 block419W4 block419S1 block419S2 block419S3 block419S4

theorem block419LeftParamsCertificate_eq_true :
    block419LeftParamsCertificate = true := by
  native_decide

theorem block419_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block419LeftL : ℝ) (block419LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block419S1 : ℝ))
    (hy2ne : y ≠ (block419S2 : ℝ))
    (hy3ne : y ≠ (block419S3 : ℝ))
    (hy4ne : y ≠ (block419S4 : ℝ)) :
    0 < block419V y := by
  have hcert := block419LeftCertificate_eq_true
  unfold block419LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block419LeftBoxes) (lo := block419LeftL) (hi := block419LeftR)
    (w1 := block419W1) (w2 := block419W2) (w3 := block419W3) (w4 := block419W4)
    (s1 := block419S1) (s2 := block419S2) (s3 := block419S3) (s4 := block419S4)
    hboxes hcover block419LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block419RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block419RightChunk000 block419W1 block419W2 block419W3 block419W4 block419S1 block419S2 block419S3 block419S4

theorem block419RightChunk000ParamsCertificate_eq_true :
    block419RightChunk000ParamsCertificate = true := by
  native_decide

theorem block419_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block419RightChunk000L : ℝ) (block419RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block419S1 : ℝ))
    (hy2ne : y ≠ (block419S2 : ℝ))
    (hy3ne : y ≠ (block419S3 : ℝ))
    (hy4ne : y ≠ (block419S4 : ℝ)) :
    0 < block419V y := by
  have hcert := block419RightChunk000Certificate_eq_true
  unfold block419RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block419RightChunk000) (lo := block419RightChunk000L) (hi := block419RightChunk000R)
    (w1 := block419W1) (w2 := block419W2) (w3 := block419W3) (w4 := block419W4)
    (s1 := block419S1) (s2 := block419S2) (s3 := block419S3) (s4 := block419S4)
    hboxes hcover block419RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block419RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block419RightChunk001 block419W1 block419W2 block419W3 block419W4 block419S1 block419S2 block419S3 block419S4

theorem block419RightChunk001ParamsCertificate_eq_true :
    block419RightChunk001ParamsCertificate = true := by
  native_decide

theorem block419_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block419RightChunk001L : ℝ) (block419RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block419S1 : ℝ))
    (hy2ne : y ≠ (block419S2 : ℝ))
    (hy3ne : y ≠ (block419S3 : ℝ))
    (hy4ne : y ≠ (block419S4 : ℝ)) :
    0 < block419V y := by
  have hcert := block419RightChunk001Certificate_eq_true
  unfold block419RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block419RightChunk001) (lo := block419RightChunk001L) (hi := block419RightChunk001R)
    (w1 := block419W1) (w2 := block419W2) (w3 := block419W3) (w4 := block419W4)
    (s1 := block419S1) (s2 := block419S2) (s3 := block419S3) (s4 := block419S4)
    hboxes hcover block419RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block419_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block419RightL : ℝ) (block419RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block419S1 : ℝ))
    (hy2ne : y ≠ (block419S2 : ℝ))
    (hy3ne : y ≠ (block419S3 : ℝ))
    (hy4ne : y ≠ (block419S4 : ℝ)) :
    0 < block419V y := by
  by_cases h0 : y ≤ (block419RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block419RightChunk000L : ℝ) (block419RightChunk000R : ℝ) := by
      have hL : (block419RightChunk000L : ℝ) = (block419RightL : ℝ) := by
        norm_num [block419RightChunk000L, block419RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block419_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    have hprev : (block419RightChunk000R : ℝ) < y := lt_of_not_ge h0
    have hL : (block419RightChunk001L : ℝ) = (block419RightChunk000R : ℝ) := by
      norm_num [block419RightChunk001L, block419RightChunk000R]
    have hR : (block419RightChunk001R : ℝ) = (block419RightR : ℝ) := by
      norm_num [block419RightChunk001R, block419RightR]
    have hyc : y ∈ Icc (block419RightChunk001L : ℝ) (block419RightChunk001R : ℝ) := by
      constructor
      · linarith [hprev, hL]
      · linarith [hy.2, hR]
    exact block419_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block419_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block419LeftL : ℝ) (block419LeftR : ℝ) →
    y ≠ 0 → y ≠ (block419S1 : ℝ) → y ≠ (block419S2 : ℝ) →
    y ≠ (block419S3 : ℝ) → y ≠ (block419S4 : ℝ) → 0 < block419V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block419RightL : ℝ) (block419RightR : ℝ) →
    y ≠ 0 → y ≠ (block419S1 : ℝ) → y ≠ (block419S2 : ℝ) →
    y ≠ (block419S3 : ℝ) → y ≠ (block419S4 : ℝ) → 0 < block419V y)

theorem block419_reallog_certificate_proof :
    block419_reallog_certificate := by
  exact ⟨block419_left_V_pos, block419_right_V_pos⟩

end Block419
end M1817475
end Erdos1038Lean
