import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block185

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block185

open Set

def block185W1 : Rat := ((17687728010870893 : Rat) / 10000000000000000)
def block185W2 : Rat := (0 : Rat)
def block185W3 : Rat := ((17667186147545003 : Rat) / 100000000000000000)
def block185W4 : Rat := ((9483816719140747 : Rat) / 100000000000000000)
def block185S1 : Rat := ((18174751 : Rat) / 10000000)
def block185S2 : Rat := ((511587 : Rat) / 200000)
def block185S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block185S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block185V (y : ℝ) : ℝ :=
  ratPotential block185W1 block185W2 block185W3 block185W4 block185S1 block185S2 block185S3 block185S4 y

def block185LeftParamsCertificate : Bool :=
  allBoxesSameParams block185LeftBoxes block185W1 block185W2 block185W3 block185W4 block185S1 block185S2 block185S3 block185S4

theorem block185LeftParamsCertificate_eq_true :
    block185LeftParamsCertificate = true := by
  native_decide

theorem block185_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block185LeftL : ℝ) (block185LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block185S1 : ℝ))
    (hy2ne : y ≠ (block185S2 : ℝ))
    (hy3ne : y ≠ (block185S3 : ℝ))
    (hy4ne : y ≠ (block185S4 : ℝ)) :
    0 < block185V y := by
  have hcert := block185LeftCertificate_eq_true
  unfold block185LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block185LeftBoxes) (lo := block185LeftL) (hi := block185LeftR)
    (w1 := block185W1) (w2 := block185W2) (w3 := block185W3) (w4 := block185W4)
    (s1 := block185S1) (s2 := block185S2) (s3 := block185S3) (s4 := block185S4)
    hboxes hcover block185LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block185RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block185RightChunk000 block185W1 block185W2 block185W3 block185W4 block185S1 block185S2 block185S3 block185S4

theorem block185RightChunk000ParamsCertificate_eq_true :
    block185RightChunk000ParamsCertificate = true := by
  native_decide

theorem block185_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block185RightChunk000L : ℝ) (block185RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block185S1 : ℝ))
    (hy2ne : y ≠ (block185S2 : ℝ))
    (hy3ne : y ≠ (block185S3 : ℝ))
    (hy4ne : y ≠ (block185S4 : ℝ)) :
    0 < block185V y := by
  have hcert := block185RightChunk000Certificate_eq_true
  unfold block185RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block185RightChunk000) (lo := block185RightChunk000L) (hi := block185RightChunk000R)
    (w1 := block185W1) (w2 := block185W2) (w3 := block185W3) (w4 := block185W4)
    (s1 := block185S1) (s2 := block185S2) (s3 := block185S3) (s4 := block185S4)
    hboxes hcover block185RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block185RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block185RightChunk001 block185W1 block185W2 block185W3 block185W4 block185S1 block185S2 block185S3 block185S4

theorem block185RightChunk001ParamsCertificate_eq_true :
    block185RightChunk001ParamsCertificate = true := by
  native_decide

theorem block185_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block185RightChunk001L : ℝ) (block185RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block185S1 : ℝ))
    (hy2ne : y ≠ (block185S2 : ℝ))
    (hy3ne : y ≠ (block185S3 : ℝ))
    (hy4ne : y ≠ (block185S4 : ℝ)) :
    0 < block185V y := by
  have hcert := block185RightChunk001Certificate_eq_true
  unfold block185RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block185RightChunk001) (lo := block185RightChunk001L) (hi := block185RightChunk001R)
    (w1 := block185W1) (w2 := block185W2) (w3 := block185W3) (w4 := block185W4)
    (s1 := block185S1) (s2 := block185S2) (s3 := block185S3) (s4 := block185S4)
    hboxes hcover block185RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block185_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block185RightL : ℝ) (block185RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block185S1 : ℝ))
    (hy2ne : y ≠ (block185S2 : ℝ))
    (hy3ne : y ≠ (block185S3 : ℝ))
    (hy4ne : y ≠ (block185S4 : ℝ)) :
    0 < block185V y := by
  by_cases h0 : y ≤ (block185RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block185RightChunk000L : ℝ) (block185RightChunk000R : ℝ) := by
      have hL : (block185RightChunk000L : ℝ) = (block185RightL : ℝ) := by
        norm_num [block185RightChunk000L, block185RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block185_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    have hprev : (block185RightChunk000R : ℝ) < y := lt_of_not_ge h0
    have hL : (block185RightChunk001L : ℝ) = (block185RightChunk000R : ℝ) := by
      norm_num [block185RightChunk001L, block185RightChunk000R]
    have hR : (block185RightChunk001R : ℝ) = (block185RightR : ℝ) := by
      norm_num [block185RightChunk001R, block185RightR]
    have hyc : y ∈ Icc (block185RightChunk001L : ℝ) (block185RightChunk001R : ℝ) := by
      constructor
      · linarith [hprev, hL]
      · linarith [hy.2, hR]
    exact block185_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block185_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block185LeftL : ℝ) (block185LeftR : ℝ) →
    y ≠ 0 → y ≠ (block185S1 : ℝ) → y ≠ (block185S2 : ℝ) →
    y ≠ (block185S3 : ℝ) → y ≠ (block185S4 : ℝ) → 0 < block185V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block185RightL : ℝ) (block185RightR : ℝ) →
    y ≠ 0 → y ≠ (block185S1 : ℝ) → y ≠ (block185S2 : ℝ) →
    y ≠ (block185S3 : ℝ) → y ≠ (block185S4 : ℝ) → 0 < block185V y)

theorem block185_reallog_certificate_proof :
    block185_reallog_certificate := by
  exact ⟨block185_left_V_pos, block185_right_V_pos⟩

end Block185
end M1817475
end Erdos1038Lean
