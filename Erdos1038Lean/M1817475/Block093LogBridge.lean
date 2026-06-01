import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block093

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block093

open Set

def block093W1 : Rat := ((3685758649934113 : Rat) / 1000000000000000)
def block093W2 : Rat := (0 : Rat)
def block093W3 : Rat := (0 : Rat)
def block093W4 : Rat := ((22902506077608767 : Rat) / 100000000000000000)
def block093S1 : Rat := ((18174751 : Rat) / 10000000)
def block093S2 : Rat := ((511587 : Rat) / 200000)
def block093S3 : Rat := ((107000619 : Rat) / 40000000)
def block093S4 : Rat := ((139214754196428566429 : Rat) / 50000000000000000000)

noncomputable def block093V (y : ℝ) : ℝ :=
  ratPotential block093W1 block093W2 block093W3 block093W4 block093S1 block093S2 block093S3 block093S4 y

def block093LeftParamsCertificate : Bool :=
  allBoxesSameParams block093LeftBoxes block093W1 block093W2 block093W3 block093W4 block093S1 block093S2 block093S3 block093S4

theorem block093LeftParamsCertificate_eq_true :
    block093LeftParamsCertificate = true := by
  native_decide

theorem block093_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block093LeftL : ℝ) (block093LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block093S1 : ℝ))
    (hy2ne : y ≠ (block093S2 : ℝ))
    (hy3ne : y ≠ (block093S3 : ℝ))
    (hy4ne : y ≠ (block093S4 : ℝ)) :
    0 < block093V y := by
  have hcert := block093LeftCertificate_eq_true
  unfold block093LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block093LeftBoxes) (lo := block093LeftL) (hi := block093LeftR)
    (w1 := block093W1) (w2 := block093W2) (w3 := block093W3) (w4 := block093W4)
    (s1 := block093S1) (s2 := block093S2) (s3 := block093S3) (s4 := block093S4)
    hboxes hcover block093LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block093RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block093RightChunk000 block093W1 block093W2 block093W3 block093W4 block093S1 block093S2 block093S3 block093S4

theorem block093RightChunk000ParamsCertificate_eq_true :
    block093RightChunk000ParamsCertificate = true := by
  native_decide

theorem block093_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block093RightChunk000L : ℝ) (block093RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block093S1 : ℝ))
    (hy2ne : y ≠ (block093S2 : ℝ))
    (hy3ne : y ≠ (block093S3 : ℝ))
    (hy4ne : y ≠ (block093S4 : ℝ)) :
    0 < block093V y := by
  have hcert := block093RightChunk000Certificate_eq_true
  unfold block093RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block093RightChunk000) (lo := block093RightChunk000L) (hi := block093RightChunk000R)
    (w1 := block093W1) (w2 := block093W2) (w3 := block093W3) (w4 := block093W4)
    (s1 := block093S1) (s2 := block093S2) (s3 := block093S3) (s4 := block093S4)
    hboxes hcover block093RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block093RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block093RightChunk001 block093W1 block093W2 block093W3 block093W4 block093S1 block093S2 block093S3 block093S4

theorem block093RightChunk001ParamsCertificate_eq_true :
    block093RightChunk001ParamsCertificate = true := by
  native_decide

theorem block093_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block093RightChunk001L : ℝ) (block093RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block093S1 : ℝ))
    (hy2ne : y ≠ (block093S2 : ℝ))
    (hy3ne : y ≠ (block093S3 : ℝ))
    (hy4ne : y ≠ (block093S4 : ℝ)) :
    0 < block093V y := by
  have hcert := block093RightChunk001Certificate_eq_true
  unfold block093RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block093RightChunk001) (lo := block093RightChunk001L) (hi := block093RightChunk001R)
    (w1 := block093W1) (w2 := block093W2) (w3 := block093W3) (w4 := block093W4)
    (s1 := block093S1) (s2 := block093S2) (s3 := block093S3) (s4 := block093S4)
    hboxes hcover block093RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block093RightChunk002ParamsCertificate : Bool :=
  allBoxesSameParams block093RightChunk002 block093W1 block093W2 block093W3 block093W4 block093S1 block093S2 block093S3 block093S4

theorem block093RightChunk002ParamsCertificate_eq_true :
    block093RightChunk002ParamsCertificate = true := by
  native_decide

theorem block093_right_chunk002_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block093RightChunk002L : ℝ) (block093RightChunk002R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block093S1 : ℝ))
    (hy2ne : y ≠ (block093S2 : ℝ))
    (hy3ne : y ≠ (block093S3 : ℝ))
    (hy4ne : y ≠ (block093S4 : ℝ)) :
    0 < block093V y := by
  have hcert := block093RightChunk002Certificate_eq_true
  unfold block093RightChunk002Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block093RightChunk002) (lo := block093RightChunk002L) (hi := block093RightChunk002R)
    (w1 := block093W1) (w2 := block093W2) (w3 := block093W3) (w4 := block093W4)
    (s1 := block093S1) (s2 := block093S2) (s3 := block093S3) (s4 := block093S4)
    hboxes hcover block093RightChunk002ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block093_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block093RightL : ℝ) (block093RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block093S1 : ℝ))
    (hy2ne : y ≠ (block093S2 : ℝ))
    (hy3ne : y ≠ (block093S3 : ℝ))
    (hy4ne : y ≠ (block093S4 : ℝ)) :
    0 < block093V y := by
  by_cases h0 : y ≤ (block093RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block093RightChunk000L : ℝ) (block093RightChunk000R : ℝ) := by
      have hL : (block093RightChunk000L : ℝ) = (block093RightL : ℝ) := by
        norm_num [block093RightChunk000L, block093RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block093_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    by_cases h1 : y ≤ (block093RightChunk001R : ℝ)
    · have hyc : y ∈ Icc (block093RightChunk001L : ℝ) (block093RightChunk001R : ℝ) := by
        have hprev : (block093RightChunk000R : ℝ) < y := lt_of_not_ge h0
        have hL : (block093RightChunk001L : ℝ) = (block093RightChunk000R : ℝ) := by
          norm_num [block093RightChunk001L, block093RightChunk000R]
        constructor
        · linarith [hprev, hL]
        · exact h1
      exact block093_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
    ·
      have hprev : (block093RightChunk001R : ℝ) < y := lt_of_not_ge h1
      have hL : (block093RightChunk002L : ℝ) = (block093RightChunk001R : ℝ) := by
        norm_num [block093RightChunk002L, block093RightChunk001R]
      have hR : (block093RightChunk002R : ℝ) = (block093RightR : ℝ) := by
        norm_num [block093RightChunk002R, block093RightR]
      have hyc : y ∈ Icc (block093RightChunk002L : ℝ) (block093RightChunk002R : ℝ) := by
        constructor
        · linarith [hprev, hL]
        · linarith [hy.2, hR]
      exact block093_right_chunk002_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block093_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block093LeftL : ℝ) (block093LeftR : ℝ) →
    y ≠ 0 → y ≠ (block093S1 : ℝ) → y ≠ (block093S2 : ℝ) →
    y ≠ (block093S3 : ℝ) → y ≠ (block093S4 : ℝ) → 0 < block093V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block093RightL : ℝ) (block093RightR : ℝ) →
    y ≠ 0 → y ≠ (block093S1 : ℝ) → y ≠ (block093S2 : ℝ) →
    y ≠ (block093S3 : ℝ) → y ≠ (block093S4 : ℝ) → 0 < block093V y)

theorem block093_reallog_certificate_proof :
    block093_reallog_certificate := by
  exact ⟨block093_left_V_pos, block093_right_V_pos⟩

end Block093
end M1817475
end Erdos1038Lean
