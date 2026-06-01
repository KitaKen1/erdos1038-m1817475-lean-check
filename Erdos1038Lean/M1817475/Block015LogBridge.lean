import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block015

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block015

open Set

def block015W1 : Rat := ((102356220420039 : Rat) / 12500000000000)
def block015W2 : Rat := (0 : Rat)
def block015W3 : Rat := (0 : Rat)
def block015W4 : Rat := ((1280028512635997 : Rat) / 5000000000000000)
def block015S1 : Rat := ((18174751 : Rat) / 10000000)
def block015S2 : Rat := ((511587 : Rat) / 200000)
def block015S3 : Rat := ((107000619 : Rat) / 40000000)
def block015S4 : Rat := ((3539260540178571301 : Rat) / 1250000000000000000)

noncomputable def block015V (y : ℝ) : ℝ :=
  ratPotential block015W1 block015W2 block015W3 block015W4 block015S1 block015S2 block015S3 block015S4 y

def block015LeftParamsCertificate : Bool :=
  allBoxesSameParams block015LeftBoxes block015W1 block015W2 block015W3 block015W4 block015S1 block015S2 block015S3 block015S4

theorem block015LeftParamsCertificate_eq_true :
    block015LeftParamsCertificate = true := by
  native_decide

theorem block015_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block015LeftL : ℝ) (block015LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block015S1 : ℝ))
    (hy2ne : y ≠ (block015S2 : ℝ))
    (hy3ne : y ≠ (block015S3 : ℝ))
    (hy4ne : y ≠ (block015S4 : ℝ)) :
    0 < block015V y := by
  have hcert := block015LeftCertificate_eq_true
  unfold block015LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block015LeftBoxes) (lo := block015LeftL) (hi := block015LeftR)
    (w1 := block015W1) (w2 := block015W2) (w3 := block015W3) (w4 := block015W4)
    (s1 := block015S1) (s2 := block015S2) (s3 := block015S3) (s4 := block015S4)
    hboxes hcover block015LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block015RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block015RightChunk000 block015W1 block015W2 block015W3 block015W4 block015S1 block015S2 block015S3 block015S4

theorem block015RightChunk000ParamsCertificate_eq_true :
    block015RightChunk000ParamsCertificate = true := by
  native_decide

theorem block015_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block015RightChunk000L : ℝ) (block015RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block015S1 : ℝ))
    (hy2ne : y ≠ (block015S2 : ℝ))
    (hy3ne : y ≠ (block015S3 : ℝ))
    (hy4ne : y ≠ (block015S4 : ℝ)) :
    0 < block015V y := by
  have hcert := block015RightChunk000Certificate_eq_true
  unfold block015RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block015RightChunk000) (lo := block015RightChunk000L) (hi := block015RightChunk000R)
    (w1 := block015W1) (w2 := block015W2) (w3 := block015W3) (w4 := block015W4)
    (s1 := block015S1) (s2 := block015S2) (s3 := block015S3) (s4 := block015S4)
    hboxes hcover block015RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block015RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block015RightChunk001 block015W1 block015W2 block015W3 block015W4 block015S1 block015S2 block015S3 block015S4

theorem block015RightChunk001ParamsCertificate_eq_true :
    block015RightChunk001ParamsCertificate = true := by
  native_decide

theorem block015_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block015RightChunk001L : ℝ) (block015RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block015S1 : ℝ))
    (hy2ne : y ≠ (block015S2 : ℝ))
    (hy3ne : y ≠ (block015S3 : ℝ))
    (hy4ne : y ≠ (block015S4 : ℝ)) :
    0 < block015V y := by
  have hcert := block015RightChunk001Certificate_eq_true
  unfold block015RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block015RightChunk001) (lo := block015RightChunk001L) (hi := block015RightChunk001R)
    (w1 := block015W1) (w2 := block015W2) (w3 := block015W3) (w4 := block015W4)
    (s1 := block015S1) (s2 := block015S2) (s3 := block015S3) (s4 := block015S4)
    hboxes hcover block015RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block015RightChunk002ParamsCertificate : Bool :=
  allBoxesSameParams block015RightChunk002 block015W1 block015W2 block015W3 block015W4 block015S1 block015S2 block015S3 block015S4

theorem block015RightChunk002ParamsCertificate_eq_true :
    block015RightChunk002ParamsCertificate = true := by
  native_decide

theorem block015_right_chunk002_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block015RightChunk002L : ℝ) (block015RightChunk002R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block015S1 : ℝ))
    (hy2ne : y ≠ (block015S2 : ℝ))
    (hy3ne : y ≠ (block015S3 : ℝ))
    (hy4ne : y ≠ (block015S4 : ℝ)) :
    0 < block015V y := by
  have hcert := block015RightChunk002Certificate_eq_true
  unfold block015RightChunk002Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block015RightChunk002) (lo := block015RightChunk002L) (hi := block015RightChunk002R)
    (w1 := block015W1) (w2 := block015W2) (w3 := block015W3) (w4 := block015W4)
    (s1 := block015S1) (s2 := block015S2) (s3 := block015S3) (s4 := block015S4)
    hboxes hcover block015RightChunk002ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block015_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block015RightL : ℝ) (block015RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block015S1 : ℝ))
    (hy2ne : y ≠ (block015S2 : ℝ))
    (hy3ne : y ≠ (block015S3 : ℝ))
    (hy4ne : y ≠ (block015S4 : ℝ)) :
    0 < block015V y := by
  by_cases h0 : y ≤ (block015RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block015RightChunk000L : ℝ) (block015RightChunk000R : ℝ) := by
      have hL : (block015RightChunk000L : ℝ) = (block015RightL : ℝ) := by
        norm_num [block015RightChunk000L, block015RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block015_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    by_cases h1 : y ≤ (block015RightChunk001R : ℝ)
    · have hyc : y ∈ Icc (block015RightChunk001L : ℝ) (block015RightChunk001R : ℝ) := by
        have hprev : (block015RightChunk000R : ℝ) < y := lt_of_not_ge h0
        have hL : (block015RightChunk001L : ℝ) = (block015RightChunk000R : ℝ) := by
          norm_num [block015RightChunk001L, block015RightChunk000R]
        constructor
        · linarith [hprev, hL]
        · exact h1
      exact block015_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
    ·
      have hprev : (block015RightChunk001R : ℝ) < y := lt_of_not_ge h1
      have hL : (block015RightChunk002L : ℝ) = (block015RightChunk001R : ℝ) := by
        norm_num [block015RightChunk002L, block015RightChunk001R]
      have hR : (block015RightChunk002R : ℝ) = (block015RightR : ℝ) := by
        norm_num [block015RightChunk002R, block015RightR]
      have hyc : y ∈ Icc (block015RightChunk002L : ℝ) (block015RightChunk002R : ℝ) := by
        constructor
        · linarith [hprev, hL]
        · linarith [hy.2, hR]
      exact block015_right_chunk002_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block015_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block015LeftL : ℝ) (block015LeftR : ℝ) →
    y ≠ 0 → y ≠ (block015S1 : ℝ) → y ≠ (block015S2 : ℝ) →
    y ≠ (block015S3 : ℝ) → y ≠ (block015S4 : ℝ) → 0 < block015V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block015RightL : ℝ) (block015RightR : ℝ) →
    y ≠ 0 → y ≠ (block015S1 : ℝ) → y ≠ (block015S2 : ℝ) →
    y ≠ (block015S3 : ℝ) → y ≠ (block015S4 : ℝ) → 0 < block015V y)

theorem block015_reallog_certificate_proof :
    block015_reallog_certificate := by
  exact ⟨block015_left_V_pos, block015_right_V_pos⟩

end Block015
end M1817475
end Erdos1038Lean
