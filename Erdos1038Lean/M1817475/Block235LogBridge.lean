import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block235

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block235

open Set

def block235W1 : Rat := ((8636132324449283 : Rat) / 10000000000000000)
def block235W2 : Rat := ((4204630752315361 : Rat) / 50000000000000000)
def block235W3 : Rat := ((9080964269216339 : Rat) / 50000000000000000)
def block235W4 : Rat := ((885857079934067 : Rat) / 12500000000000000)
def block235S1 : Rat := ((18174751 : Rat) / 10000000)
def block235S2 : Rat := ((511587 : Rat) / 200000)
def block235S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block235S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block235V (y : ℝ) : ℝ :=
  ratPotential block235W1 block235W2 block235W3 block235W4 block235S1 block235S2 block235S3 block235S4 y

def block235LeftParamsCertificate : Bool :=
  allBoxesSameParams block235LeftBoxes block235W1 block235W2 block235W3 block235W4 block235S1 block235S2 block235S3 block235S4

theorem block235LeftParamsCertificate_eq_true :
    block235LeftParamsCertificate = true := by
  native_decide

theorem block235_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block235LeftL : ℝ) (block235LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block235S1 : ℝ))
    (hy2ne : y ≠ (block235S2 : ℝ))
    (hy3ne : y ≠ (block235S3 : ℝ))
    (hy4ne : y ≠ (block235S4 : ℝ)) :
    0 < block235V y := by
  have hcert := block235LeftCertificate_eq_true
  unfold block235LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block235LeftBoxes) (lo := block235LeftL) (hi := block235LeftR)
    (w1 := block235W1) (w2 := block235W2) (w3 := block235W3) (w4 := block235W4)
    (s1 := block235S1) (s2 := block235S2) (s3 := block235S3) (s4 := block235S4)
    hboxes hcover block235LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block235RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block235RightChunk000 block235W1 block235W2 block235W3 block235W4 block235S1 block235S2 block235S3 block235S4

theorem block235RightChunk000ParamsCertificate_eq_true :
    block235RightChunk000ParamsCertificate = true := by
  native_decide

theorem block235_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block235RightChunk000L : ℝ) (block235RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block235S1 : ℝ))
    (hy2ne : y ≠ (block235S2 : ℝ))
    (hy3ne : y ≠ (block235S3 : ℝ))
    (hy4ne : y ≠ (block235S4 : ℝ)) :
    0 < block235V y := by
  have hcert := block235RightChunk000Certificate_eq_true
  unfold block235RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block235RightChunk000) (lo := block235RightChunk000L) (hi := block235RightChunk000R)
    (w1 := block235W1) (w2 := block235W2) (w3 := block235W3) (w4 := block235W4)
    (s1 := block235S1) (s2 := block235S2) (s3 := block235S3) (s4 := block235S4)
    hboxes hcover block235RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block235RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block235RightChunk001 block235W1 block235W2 block235W3 block235W4 block235S1 block235S2 block235S3 block235S4

theorem block235RightChunk001ParamsCertificate_eq_true :
    block235RightChunk001ParamsCertificate = true := by
  native_decide

theorem block235_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block235RightChunk001L : ℝ) (block235RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block235S1 : ℝ))
    (hy2ne : y ≠ (block235S2 : ℝ))
    (hy3ne : y ≠ (block235S3 : ℝ))
    (hy4ne : y ≠ (block235S4 : ℝ)) :
    0 < block235V y := by
  have hcert := block235RightChunk001Certificate_eq_true
  unfold block235RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block235RightChunk001) (lo := block235RightChunk001L) (hi := block235RightChunk001R)
    (w1 := block235W1) (w2 := block235W2) (w3 := block235W3) (w4 := block235W4)
    (s1 := block235S1) (s2 := block235S2) (s3 := block235S3) (s4 := block235S4)
    hboxes hcover block235RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block235RightChunk002ParamsCertificate : Bool :=
  allBoxesSameParams block235RightChunk002 block235W1 block235W2 block235W3 block235W4 block235S1 block235S2 block235S3 block235S4

theorem block235RightChunk002ParamsCertificate_eq_true :
    block235RightChunk002ParamsCertificate = true := by
  native_decide

theorem block235_right_chunk002_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block235RightChunk002L : ℝ) (block235RightChunk002R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block235S1 : ℝ))
    (hy2ne : y ≠ (block235S2 : ℝ))
    (hy3ne : y ≠ (block235S3 : ℝ))
    (hy4ne : y ≠ (block235S4 : ℝ)) :
    0 < block235V y := by
  have hcert := block235RightChunk002Certificate_eq_true
  unfold block235RightChunk002Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block235RightChunk002) (lo := block235RightChunk002L) (hi := block235RightChunk002R)
    (w1 := block235W1) (w2 := block235W2) (w3 := block235W3) (w4 := block235W4)
    (s1 := block235S1) (s2 := block235S2) (s3 := block235S3) (s4 := block235S4)
    hboxes hcover block235RightChunk002ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block235_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block235RightL : ℝ) (block235RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block235S1 : ℝ))
    (hy2ne : y ≠ (block235S2 : ℝ))
    (hy3ne : y ≠ (block235S3 : ℝ))
    (hy4ne : y ≠ (block235S4 : ℝ)) :
    0 < block235V y := by
  by_cases h0 : y ≤ (block235RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block235RightChunk000L : ℝ) (block235RightChunk000R : ℝ) := by
      have hL : (block235RightChunk000L : ℝ) = (block235RightL : ℝ) := by
        norm_num [block235RightChunk000L, block235RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block235_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    by_cases h1 : y ≤ (block235RightChunk001R : ℝ)
    · have hyc : y ∈ Icc (block235RightChunk001L : ℝ) (block235RightChunk001R : ℝ) := by
        have hprev : (block235RightChunk000R : ℝ) < y := lt_of_not_ge h0
        have hL : (block235RightChunk001L : ℝ) = (block235RightChunk000R : ℝ) := by
          norm_num [block235RightChunk001L, block235RightChunk000R]
        constructor
        · linarith [hprev, hL]
        · exact h1
      exact block235_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
    ·
      have hprev : (block235RightChunk001R : ℝ) < y := lt_of_not_ge h1
      have hL : (block235RightChunk002L : ℝ) = (block235RightChunk001R : ℝ) := by
        norm_num [block235RightChunk002L, block235RightChunk001R]
      have hR : (block235RightChunk002R : ℝ) = (block235RightR : ℝ) := by
        norm_num [block235RightChunk002R, block235RightR]
      have hyc : y ∈ Icc (block235RightChunk002L : ℝ) (block235RightChunk002R : ℝ) := by
        constructor
        · linarith [hprev, hL]
        · linarith [hy.2, hR]
      exact block235_right_chunk002_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block235_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block235LeftL : ℝ) (block235LeftR : ℝ) →
    y ≠ 0 → y ≠ (block235S1 : ℝ) → y ≠ (block235S2 : ℝ) →
    y ≠ (block235S3 : ℝ) → y ≠ (block235S4 : ℝ) → 0 < block235V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block235RightL : ℝ) (block235RightR : ℝ) →
    y ≠ 0 → y ≠ (block235S1 : ℝ) → y ≠ (block235S2 : ℝ) →
    y ≠ (block235S3 : ℝ) → y ≠ (block235S4 : ℝ) → 0 < block235V y)

theorem block235_reallog_certificate_proof :
    block235_reallog_certificate := by
  exact ⟨block235_left_V_pos, block235_right_V_pos⟩

end Block235
end M1817475
end Erdos1038Lean
