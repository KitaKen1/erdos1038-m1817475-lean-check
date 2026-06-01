import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block216

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block216

open Set

def block216W1 : Rat := ((9626282071756319 : Rat) / 10000000000000000)
def block216W2 : Rat := ((677519362722343 : Rat) / 12500000000000000)
def block216W3 : Rat := ((434376577697243 : Rat) / 2500000000000000)
def block216W4 : Rat := ((2452432270646381 : Rat) / 25000000000000000)
def block216S1 : Rat := ((18174751 : Rat) / 10000000)
def block216S2 : Rat := ((511587 : Rat) / 200000)
def block216S3 : Rat := ((135344025982142857073 : Rat) / 50000000000000000000)
def block216S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block216V (y : ℝ) : ℝ :=
  ratPotential block216W1 block216W2 block216W3 block216W4 block216S1 block216S2 block216S3 block216S4 y

def block216LeftParamsCertificate : Bool :=
  allBoxesSameParams block216LeftBoxes block216W1 block216W2 block216W3 block216W4 block216S1 block216S2 block216S3 block216S4

theorem block216LeftParamsCertificate_eq_true :
    block216LeftParamsCertificate = true := by
  native_decide

theorem block216_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block216LeftL : ℝ) (block216LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block216S1 : ℝ))
    (hy2ne : y ≠ (block216S2 : ℝ))
    (hy3ne : y ≠ (block216S3 : ℝ))
    (hy4ne : y ≠ (block216S4 : ℝ)) :
    0 < block216V y := by
  have hcert := block216LeftCertificate_eq_true
  unfold block216LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block216LeftBoxes) (lo := block216LeftL) (hi := block216LeftR)
    (w1 := block216W1) (w2 := block216W2) (w3 := block216W3) (w4 := block216W4)
    (s1 := block216S1) (s2 := block216S2) (s3 := block216S3) (s4 := block216S4)
    hboxes hcover block216LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block216RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block216RightChunk000 block216W1 block216W2 block216W3 block216W4 block216S1 block216S2 block216S3 block216S4

theorem block216RightChunk000ParamsCertificate_eq_true :
    block216RightChunk000ParamsCertificate = true := by
  native_decide

theorem block216_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block216RightChunk000L : ℝ) (block216RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block216S1 : ℝ))
    (hy2ne : y ≠ (block216S2 : ℝ))
    (hy3ne : y ≠ (block216S3 : ℝ))
    (hy4ne : y ≠ (block216S4 : ℝ)) :
    0 < block216V y := by
  have hcert := block216RightChunk000Certificate_eq_true
  unfold block216RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block216RightChunk000) (lo := block216RightChunk000L) (hi := block216RightChunk000R)
    (w1 := block216W1) (w2 := block216W2) (w3 := block216W3) (w4 := block216W4)
    (s1 := block216S1) (s2 := block216S2) (s3 := block216S3) (s4 := block216S4)
    hboxes hcover block216RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block216RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block216RightChunk001 block216W1 block216W2 block216W3 block216W4 block216S1 block216S2 block216S3 block216S4

theorem block216RightChunk001ParamsCertificate_eq_true :
    block216RightChunk001ParamsCertificate = true := by
  native_decide

theorem block216_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block216RightChunk001L : ℝ) (block216RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block216S1 : ℝ))
    (hy2ne : y ≠ (block216S2 : ℝ))
    (hy3ne : y ≠ (block216S3 : ℝ))
    (hy4ne : y ≠ (block216S4 : ℝ)) :
    0 < block216V y := by
  have hcert := block216RightChunk001Certificate_eq_true
  unfold block216RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block216RightChunk001) (lo := block216RightChunk001L) (hi := block216RightChunk001R)
    (w1 := block216W1) (w2 := block216W2) (w3 := block216W3) (w4 := block216W4)
    (s1 := block216S1) (s2 := block216S2) (s3 := block216S3) (s4 := block216S4)
    hboxes hcover block216RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block216RightChunk002ParamsCertificate : Bool :=
  allBoxesSameParams block216RightChunk002 block216W1 block216W2 block216W3 block216W4 block216S1 block216S2 block216S3 block216S4

theorem block216RightChunk002ParamsCertificate_eq_true :
    block216RightChunk002ParamsCertificate = true := by
  native_decide

theorem block216_right_chunk002_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block216RightChunk002L : ℝ) (block216RightChunk002R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block216S1 : ℝ))
    (hy2ne : y ≠ (block216S2 : ℝ))
    (hy3ne : y ≠ (block216S3 : ℝ))
    (hy4ne : y ≠ (block216S4 : ℝ)) :
    0 < block216V y := by
  have hcert := block216RightChunk002Certificate_eq_true
  unfold block216RightChunk002Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block216RightChunk002) (lo := block216RightChunk002L) (hi := block216RightChunk002R)
    (w1 := block216W1) (w2 := block216W2) (w3 := block216W3) (w4 := block216W4)
    (s1 := block216S1) (s2 := block216S2) (s3 := block216S3) (s4 := block216S4)
    hboxes hcover block216RightChunk002ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block216_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block216RightL : ℝ) (block216RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block216S1 : ℝ))
    (hy2ne : y ≠ (block216S2 : ℝ))
    (hy3ne : y ≠ (block216S3 : ℝ))
    (hy4ne : y ≠ (block216S4 : ℝ)) :
    0 < block216V y := by
  by_cases h0 : y ≤ (block216RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block216RightChunk000L : ℝ) (block216RightChunk000R : ℝ) := by
      have hL : (block216RightChunk000L : ℝ) = (block216RightL : ℝ) := by
        norm_num [block216RightChunk000L, block216RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block216_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    by_cases h1 : y ≤ (block216RightChunk001R : ℝ)
    · have hyc : y ∈ Icc (block216RightChunk001L : ℝ) (block216RightChunk001R : ℝ) := by
        have hprev : (block216RightChunk000R : ℝ) < y := lt_of_not_ge h0
        have hL : (block216RightChunk001L : ℝ) = (block216RightChunk000R : ℝ) := by
          norm_num [block216RightChunk001L, block216RightChunk000R]
        constructor
        · linarith [hprev, hL]
        · exact h1
      exact block216_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
    ·
      have hprev : (block216RightChunk001R : ℝ) < y := lt_of_not_ge h1
      have hL : (block216RightChunk002L : ℝ) = (block216RightChunk001R : ℝ) := by
        norm_num [block216RightChunk002L, block216RightChunk001R]
      have hR : (block216RightChunk002R : ℝ) = (block216RightR : ℝ) := by
        norm_num [block216RightChunk002R, block216RightR]
      have hyc : y ∈ Icc (block216RightChunk002L : ℝ) (block216RightChunk002R : ℝ) := by
        constructor
        · linarith [hprev, hL]
        · linarith [hy.2, hR]
      exact block216_right_chunk002_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block216_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block216LeftL : ℝ) (block216LeftR : ℝ) →
    y ≠ 0 → y ≠ (block216S1 : ℝ) → y ≠ (block216S2 : ℝ) →
    y ≠ (block216S3 : ℝ) → y ≠ (block216S4 : ℝ) → 0 < block216V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block216RightL : ℝ) (block216RightR : ℝ) →
    y ≠ 0 → y ≠ (block216S1 : ℝ) → y ≠ (block216S2 : ℝ) →
    y ≠ (block216S3 : ℝ) → y ≠ (block216S4 : ℝ) → 0 < block216V y)

theorem block216_reallog_certificate_proof :
    block216_reallog_certificate := by
  exact ⟨block216_left_V_pos, block216_right_V_pos⟩

end Block216
end M1817475
end Erdos1038Lean
