import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block220

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block220

open Set

def block220W1 : Rat := ((4799335792499607 : Rat) / 5000000000000000)
def block220W2 : Rat := ((2202905509282643 : Rat) / 40000000000000000)
def block220W3 : Rat := ((4315681732193473 : Rat) / 25000000000000000)
def block220W4 : Rat := ((2466162672111679 : Rat) / 25000000000000000)
def block220S1 : Rat := ((18174751 : Rat) / 10000000)
def block220S2 : Rat := ((511587 : Rat) / 200000)
def block220S3 : Rat := ((135344025982142857073 : Rat) / 50000000000000000000)
def block220S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block220V (y : ℝ) : ℝ :=
  ratPotential block220W1 block220W2 block220W3 block220W4 block220S1 block220S2 block220S3 block220S4 y

def block220LeftParamsCertificate : Bool :=
  allBoxesSameParams block220LeftBoxes block220W1 block220W2 block220W3 block220W4 block220S1 block220S2 block220S3 block220S4

theorem block220LeftParamsCertificate_eq_true :
    block220LeftParamsCertificate = true := by
  native_decide

theorem block220_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block220LeftL : ℝ) (block220LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block220S1 : ℝ))
    (hy2ne : y ≠ (block220S2 : ℝ))
    (hy3ne : y ≠ (block220S3 : ℝ))
    (hy4ne : y ≠ (block220S4 : ℝ)) :
    0 < block220V y := by
  have hcert := block220LeftCertificate_eq_true
  unfold block220LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block220LeftBoxes) (lo := block220LeftL) (hi := block220LeftR)
    (w1 := block220W1) (w2 := block220W2) (w3 := block220W3) (w4 := block220W4)
    (s1 := block220S1) (s2 := block220S2) (s3 := block220S3) (s4 := block220S4)
    hboxes hcover block220LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block220RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block220RightChunk000 block220W1 block220W2 block220W3 block220W4 block220S1 block220S2 block220S3 block220S4

theorem block220RightChunk000ParamsCertificate_eq_true :
    block220RightChunk000ParamsCertificate = true := by
  native_decide

theorem block220_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block220RightChunk000L : ℝ) (block220RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block220S1 : ℝ))
    (hy2ne : y ≠ (block220S2 : ℝ))
    (hy3ne : y ≠ (block220S3 : ℝ))
    (hy4ne : y ≠ (block220S4 : ℝ)) :
    0 < block220V y := by
  have hcert := block220RightChunk000Certificate_eq_true
  unfold block220RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block220RightChunk000) (lo := block220RightChunk000L) (hi := block220RightChunk000R)
    (w1 := block220W1) (w2 := block220W2) (w3 := block220W3) (w4 := block220W4)
    (s1 := block220S1) (s2 := block220S2) (s3 := block220S3) (s4 := block220S4)
    hboxes hcover block220RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block220RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block220RightChunk001 block220W1 block220W2 block220W3 block220W4 block220S1 block220S2 block220S3 block220S4

theorem block220RightChunk001ParamsCertificate_eq_true :
    block220RightChunk001ParamsCertificate = true := by
  native_decide

theorem block220_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block220RightChunk001L : ℝ) (block220RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block220S1 : ℝ))
    (hy2ne : y ≠ (block220S2 : ℝ))
    (hy3ne : y ≠ (block220S3 : ℝ))
    (hy4ne : y ≠ (block220S4 : ℝ)) :
    0 < block220V y := by
  have hcert := block220RightChunk001Certificate_eq_true
  unfold block220RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block220RightChunk001) (lo := block220RightChunk001L) (hi := block220RightChunk001R)
    (w1 := block220W1) (w2 := block220W2) (w3 := block220W3) (w4 := block220W4)
    (s1 := block220S1) (s2 := block220S2) (s3 := block220S3) (s4 := block220S4)
    hboxes hcover block220RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block220RightChunk002ParamsCertificate : Bool :=
  allBoxesSameParams block220RightChunk002 block220W1 block220W2 block220W3 block220W4 block220S1 block220S2 block220S3 block220S4

theorem block220RightChunk002ParamsCertificate_eq_true :
    block220RightChunk002ParamsCertificate = true := by
  native_decide

theorem block220_right_chunk002_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block220RightChunk002L : ℝ) (block220RightChunk002R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block220S1 : ℝ))
    (hy2ne : y ≠ (block220S2 : ℝ))
    (hy3ne : y ≠ (block220S3 : ℝ))
    (hy4ne : y ≠ (block220S4 : ℝ)) :
    0 < block220V y := by
  have hcert := block220RightChunk002Certificate_eq_true
  unfold block220RightChunk002Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block220RightChunk002) (lo := block220RightChunk002L) (hi := block220RightChunk002R)
    (w1 := block220W1) (w2 := block220W2) (w3 := block220W3) (w4 := block220W4)
    (s1 := block220S1) (s2 := block220S2) (s3 := block220S3) (s4 := block220S4)
    hboxes hcover block220RightChunk002ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block220_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block220RightL : ℝ) (block220RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block220S1 : ℝ))
    (hy2ne : y ≠ (block220S2 : ℝ))
    (hy3ne : y ≠ (block220S3 : ℝ))
    (hy4ne : y ≠ (block220S4 : ℝ)) :
    0 < block220V y := by
  by_cases h0 : y ≤ (block220RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block220RightChunk000L : ℝ) (block220RightChunk000R : ℝ) := by
      have hL : (block220RightChunk000L : ℝ) = (block220RightL : ℝ) := by
        norm_num [block220RightChunk000L, block220RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block220_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    by_cases h1 : y ≤ (block220RightChunk001R : ℝ)
    · have hyc : y ∈ Icc (block220RightChunk001L : ℝ) (block220RightChunk001R : ℝ) := by
        have hprev : (block220RightChunk000R : ℝ) < y := lt_of_not_ge h0
        have hL : (block220RightChunk001L : ℝ) = (block220RightChunk000R : ℝ) := by
          norm_num [block220RightChunk001L, block220RightChunk000R]
        constructor
        · linarith [hprev, hL]
        · exact h1
      exact block220_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
    ·
      have hprev : (block220RightChunk001R : ℝ) < y := lt_of_not_ge h1
      have hL : (block220RightChunk002L : ℝ) = (block220RightChunk001R : ℝ) := by
        norm_num [block220RightChunk002L, block220RightChunk001R]
      have hR : (block220RightChunk002R : ℝ) = (block220RightR : ℝ) := by
        norm_num [block220RightChunk002R, block220RightR]
      have hyc : y ∈ Icc (block220RightChunk002L : ℝ) (block220RightChunk002R : ℝ) := by
        constructor
        · linarith [hprev, hL]
        · linarith [hy.2, hR]
      exact block220_right_chunk002_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block220_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block220LeftL : ℝ) (block220LeftR : ℝ) →
    y ≠ 0 → y ≠ (block220S1 : ℝ) → y ≠ (block220S2 : ℝ) →
    y ≠ (block220S3 : ℝ) → y ≠ (block220S4 : ℝ) → 0 < block220V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block220RightL : ℝ) (block220RightR : ℝ) →
    y ≠ 0 → y ≠ (block220S1 : ℝ) → y ≠ (block220S2 : ℝ) →
    y ≠ (block220S3 : ℝ) → y ≠ (block220S4 : ℝ) → 0 < block220V y)

theorem block220_reallog_certificate_proof :
    block220_reallog_certificate := by
  exact ⟨block220_left_V_pos, block220_right_V_pos⟩

end Block220
end M1817475
end Erdos1038Lean
