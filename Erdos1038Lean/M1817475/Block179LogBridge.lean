import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block179

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block179

open Set

def block179W1 : Rat := ((17900987592958477 : Rat) / 10000000000000000)
def block179W2 : Rat := (0 : Rat)
def block179W3 : Rat := ((346253810658439 : Rat) / 2000000000000000)
def block179W4 : Rat := ((4866613407571291 : Rat) / 50000000000000000)
def block179S1 : Rat := ((18174751 : Rat) / 10000000)
def block179S2 : Rat := ((511587 : Rat) / 200000)
def block179S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block179S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block179V (y : ℝ) : ℝ :=
  ratPotential block179W1 block179W2 block179W3 block179W4 block179S1 block179S2 block179S3 block179S4 y

def block179LeftParamsCertificate : Bool :=
  allBoxesSameParams block179LeftBoxes block179W1 block179W2 block179W3 block179W4 block179S1 block179S2 block179S3 block179S4

theorem block179LeftParamsCertificate_eq_true :
    block179LeftParamsCertificate = true := by
  native_decide

theorem block179_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block179LeftL : ℝ) (block179LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block179S1 : ℝ))
    (hy2ne : y ≠ (block179S2 : ℝ))
    (hy3ne : y ≠ (block179S3 : ℝ))
    (hy4ne : y ≠ (block179S4 : ℝ)) :
    0 < block179V y := by
  have hcert := block179LeftCertificate_eq_true
  unfold block179LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block179LeftBoxes) (lo := block179LeftL) (hi := block179LeftR)
    (w1 := block179W1) (w2 := block179W2) (w3 := block179W3) (w4 := block179W4)
    (s1 := block179S1) (s2 := block179S2) (s3 := block179S3) (s4 := block179S4)
    hboxes hcover block179LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block179RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block179RightChunk000 block179W1 block179W2 block179W3 block179W4 block179S1 block179S2 block179S3 block179S4

theorem block179RightChunk000ParamsCertificate_eq_true :
    block179RightChunk000ParamsCertificate = true := by
  native_decide

theorem block179_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block179RightChunk000L : ℝ) (block179RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block179S1 : ℝ))
    (hy2ne : y ≠ (block179S2 : ℝ))
    (hy3ne : y ≠ (block179S3 : ℝ))
    (hy4ne : y ≠ (block179S4 : ℝ)) :
    0 < block179V y := by
  have hcert := block179RightChunk000Certificate_eq_true
  unfold block179RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block179RightChunk000) (lo := block179RightChunk000L) (hi := block179RightChunk000R)
    (w1 := block179W1) (w2 := block179W2) (w3 := block179W3) (w4 := block179W4)
    (s1 := block179S1) (s2 := block179S2) (s3 := block179S3) (s4 := block179S4)
    hboxes hcover block179RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block179RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block179RightChunk001 block179W1 block179W2 block179W3 block179W4 block179S1 block179S2 block179S3 block179S4

theorem block179RightChunk001ParamsCertificate_eq_true :
    block179RightChunk001ParamsCertificate = true := by
  native_decide

theorem block179_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block179RightChunk001L : ℝ) (block179RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block179S1 : ℝ))
    (hy2ne : y ≠ (block179S2 : ℝ))
    (hy3ne : y ≠ (block179S3 : ℝ))
    (hy4ne : y ≠ (block179S4 : ℝ)) :
    0 < block179V y := by
  have hcert := block179RightChunk001Certificate_eq_true
  unfold block179RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block179RightChunk001) (lo := block179RightChunk001L) (hi := block179RightChunk001R)
    (w1 := block179W1) (w2 := block179W2) (w3 := block179W3) (w4 := block179W4)
    (s1 := block179S1) (s2 := block179S2) (s3 := block179S3) (s4 := block179S4)
    hboxes hcover block179RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block179_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block179RightL : ℝ) (block179RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block179S1 : ℝ))
    (hy2ne : y ≠ (block179S2 : ℝ))
    (hy3ne : y ≠ (block179S3 : ℝ))
    (hy4ne : y ≠ (block179S4 : ℝ)) :
    0 < block179V y := by
  by_cases h0 : y ≤ (block179RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block179RightChunk000L : ℝ) (block179RightChunk000R : ℝ) := by
      have hL : (block179RightChunk000L : ℝ) = (block179RightL : ℝ) := by
        norm_num [block179RightChunk000L, block179RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block179_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    have hprev : (block179RightChunk000R : ℝ) < y := lt_of_not_ge h0
    have hL : (block179RightChunk001L : ℝ) = (block179RightChunk000R : ℝ) := by
      norm_num [block179RightChunk001L, block179RightChunk000R]
    have hR : (block179RightChunk001R : ℝ) = (block179RightR : ℝ) := by
      norm_num [block179RightChunk001R, block179RightR]
    have hyc : y ∈ Icc (block179RightChunk001L : ℝ) (block179RightChunk001R : ℝ) := by
      constructor
      · linarith [hprev, hL]
      · linarith [hy.2, hR]
    exact block179_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block179_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block179LeftL : ℝ) (block179LeftR : ℝ) →
    y ≠ 0 → y ≠ (block179S1 : ℝ) → y ≠ (block179S2 : ℝ) →
    y ≠ (block179S3 : ℝ) → y ≠ (block179S4 : ℝ) → 0 < block179V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block179RightL : ℝ) (block179RightR : ℝ) →
    y ≠ 0 → y ≠ (block179S1 : ℝ) → y ≠ (block179S2 : ℝ) →
    y ≠ (block179S3 : ℝ) → y ≠ (block179S4 : ℝ) → 0 < block179V y)

theorem block179_reallog_certificate_proof :
    block179_reallog_certificate := by
  exact ⟨block179_left_V_pos, block179_right_V_pos⟩

end Block179
end M1817475
end Erdos1038Lean
