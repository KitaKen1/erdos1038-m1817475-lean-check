import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block222

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block222

open Set

def block222W1 : Rat := ((4794378756733327 : Rat) / 5000000000000000)
def block222W2 : Rat := ((27697060089278483 : Rat) / 500000000000000000)
def block222W3 : Rat := ((8610883933904473 : Rat) / 50000000000000000)
def block222W4 : Rat := ((1977000216673569 : Rat) / 20000000000000000)
def block222S1 : Rat := ((18174751 : Rat) / 10000000)
def block222S2 : Rat := ((511587 : Rat) / 200000)
def block222S3 : Rat := ((135344025982142857073 : Rat) / 50000000000000000000)
def block222S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block222V (y : ℝ) : ℝ :=
  ratPotential block222W1 block222W2 block222W3 block222W4 block222S1 block222S2 block222S3 block222S4 y

def block222LeftParamsCertificate : Bool :=
  allBoxesSameParams block222LeftBoxes block222W1 block222W2 block222W3 block222W4 block222S1 block222S2 block222S3 block222S4

theorem block222LeftParamsCertificate_eq_true :
    block222LeftParamsCertificate = true := by
  native_decide

theorem block222_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block222LeftL : ℝ) (block222LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block222S1 : ℝ))
    (hy2ne : y ≠ (block222S2 : ℝ))
    (hy3ne : y ≠ (block222S3 : ℝ))
    (hy4ne : y ≠ (block222S4 : ℝ)) :
    0 < block222V y := by
  have hcert := block222LeftCertificate_eq_true
  unfold block222LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block222LeftBoxes) (lo := block222LeftL) (hi := block222LeftR)
    (w1 := block222W1) (w2 := block222W2) (w3 := block222W3) (w4 := block222W4)
    (s1 := block222S1) (s2 := block222S2) (s3 := block222S3) (s4 := block222S4)
    hboxes hcover block222LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block222RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block222RightChunk000 block222W1 block222W2 block222W3 block222W4 block222S1 block222S2 block222S3 block222S4

theorem block222RightChunk000ParamsCertificate_eq_true :
    block222RightChunk000ParamsCertificate = true := by
  native_decide

theorem block222_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block222RightChunk000L : ℝ) (block222RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block222S1 : ℝ))
    (hy2ne : y ≠ (block222S2 : ℝ))
    (hy3ne : y ≠ (block222S3 : ℝ))
    (hy4ne : y ≠ (block222S4 : ℝ)) :
    0 < block222V y := by
  have hcert := block222RightChunk000Certificate_eq_true
  unfold block222RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block222RightChunk000) (lo := block222RightChunk000L) (hi := block222RightChunk000R)
    (w1 := block222W1) (w2 := block222W2) (w3 := block222W3) (w4 := block222W4)
    (s1 := block222S1) (s2 := block222S2) (s3 := block222S3) (s4 := block222S4)
    hboxes hcover block222RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block222RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block222RightChunk001 block222W1 block222W2 block222W3 block222W4 block222S1 block222S2 block222S3 block222S4

theorem block222RightChunk001ParamsCertificate_eq_true :
    block222RightChunk001ParamsCertificate = true := by
  native_decide

theorem block222_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block222RightChunk001L : ℝ) (block222RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block222S1 : ℝ))
    (hy2ne : y ≠ (block222S2 : ℝ))
    (hy3ne : y ≠ (block222S3 : ℝ))
    (hy4ne : y ≠ (block222S4 : ℝ)) :
    0 < block222V y := by
  have hcert := block222RightChunk001Certificate_eq_true
  unfold block222RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block222RightChunk001) (lo := block222RightChunk001L) (hi := block222RightChunk001R)
    (w1 := block222W1) (w2 := block222W2) (w3 := block222W3) (w4 := block222W4)
    (s1 := block222S1) (s2 := block222S2) (s3 := block222S3) (s4 := block222S4)
    hboxes hcover block222RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block222RightChunk002ParamsCertificate : Bool :=
  allBoxesSameParams block222RightChunk002 block222W1 block222W2 block222W3 block222W4 block222S1 block222S2 block222S3 block222S4

theorem block222RightChunk002ParamsCertificate_eq_true :
    block222RightChunk002ParamsCertificate = true := by
  native_decide

theorem block222_right_chunk002_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block222RightChunk002L : ℝ) (block222RightChunk002R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block222S1 : ℝ))
    (hy2ne : y ≠ (block222S2 : ℝ))
    (hy3ne : y ≠ (block222S3 : ℝ))
    (hy4ne : y ≠ (block222S4 : ℝ)) :
    0 < block222V y := by
  have hcert := block222RightChunk002Certificate_eq_true
  unfold block222RightChunk002Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block222RightChunk002) (lo := block222RightChunk002L) (hi := block222RightChunk002R)
    (w1 := block222W1) (w2 := block222W2) (w3 := block222W3) (w4 := block222W4)
    (s1 := block222S1) (s2 := block222S2) (s3 := block222S3) (s4 := block222S4)
    hboxes hcover block222RightChunk002ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block222_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block222RightL : ℝ) (block222RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block222S1 : ℝ))
    (hy2ne : y ≠ (block222S2 : ℝ))
    (hy3ne : y ≠ (block222S3 : ℝ))
    (hy4ne : y ≠ (block222S4 : ℝ)) :
    0 < block222V y := by
  by_cases h0 : y ≤ (block222RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block222RightChunk000L : ℝ) (block222RightChunk000R : ℝ) := by
      have hL : (block222RightChunk000L : ℝ) = (block222RightL : ℝ) := by
        norm_num [block222RightChunk000L, block222RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block222_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    by_cases h1 : y ≤ (block222RightChunk001R : ℝ)
    · have hyc : y ∈ Icc (block222RightChunk001L : ℝ) (block222RightChunk001R : ℝ) := by
        have hprev : (block222RightChunk000R : ℝ) < y := lt_of_not_ge h0
        have hL : (block222RightChunk001L : ℝ) = (block222RightChunk000R : ℝ) := by
          norm_num [block222RightChunk001L, block222RightChunk000R]
        constructor
        · linarith [hprev, hL]
        · exact h1
      exact block222_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
    ·
      have hprev : (block222RightChunk001R : ℝ) < y := lt_of_not_ge h1
      have hL : (block222RightChunk002L : ℝ) = (block222RightChunk001R : ℝ) := by
        norm_num [block222RightChunk002L, block222RightChunk001R]
      have hR : (block222RightChunk002R : ℝ) = (block222RightR : ℝ) := by
        norm_num [block222RightChunk002R, block222RightR]
      have hyc : y ∈ Icc (block222RightChunk002L : ℝ) (block222RightChunk002R : ℝ) := by
        constructor
        · linarith [hprev, hL]
        · linarith [hy.2, hR]
      exact block222_right_chunk002_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block222_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block222LeftL : ℝ) (block222LeftR : ℝ) →
    y ≠ 0 → y ≠ (block222S1 : ℝ) → y ≠ (block222S2 : ℝ) →
    y ≠ (block222S3 : ℝ) → y ≠ (block222S4 : ℝ) → 0 < block222V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block222RightL : ℝ) (block222RightR : ℝ) →
    y ≠ 0 → y ≠ (block222S1 : ℝ) → y ≠ (block222S2 : ℝ) →
    y ≠ (block222S3 : ℝ) → y ≠ (block222S4 : ℝ) → 0 < block222V y)

theorem block222_reallog_certificate_proof :
    block222_reallog_certificate := by
  exact ⟨block222_left_V_pos, block222_right_V_pos⟩

end Block222
end M1817475
end Erdos1038Lean
