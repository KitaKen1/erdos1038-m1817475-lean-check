import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block245

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block245

open Set

def block245W1 : Rat := ((2142968536717019 : Rat) / 2500000000000000)
def block245W2 : Rat := ((8583159785145679 : Rat) / 100000000000000000)
def block245W3 : Rat := ((1049966533573477 : Rat) / 25000000000000000)
def block245W4 : Rat := ((2610548285145543 : Rat) / 12500000000000000)
def block245S1 : Rat := ((18174751 : Rat) / 10000000)
def block245S2 : Rat := ((511587 : Rat) / 200000)
def block245S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block245S4 : Rat := ((3421965897321428449 : Rat) / 1250000000000000000)

noncomputable def block245V (y : ℝ) : ℝ :=
  ratPotential block245W1 block245W2 block245W3 block245W4 block245S1 block245S2 block245S3 block245S4 y

def block245LeftParamsCertificate : Bool :=
  allBoxesSameParams block245LeftBoxes block245W1 block245W2 block245W3 block245W4 block245S1 block245S2 block245S3 block245S4

theorem block245LeftParamsCertificate_eq_true :
    block245LeftParamsCertificate = true := by
  native_decide

theorem block245_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block245LeftL : ℝ) (block245LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block245S1 : ℝ))
    (hy2ne : y ≠ (block245S2 : ℝ))
    (hy3ne : y ≠ (block245S3 : ℝ))
    (hy4ne : y ≠ (block245S4 : ℝ)) :
    0 < block245V y := by
  have hcert := block245LeftCertificate_eq_true
  unfold block245LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block245LeftBoxes) (lo := block245LeftL) (hi := block245LeftR)
    (w1 := block245W1) (w2 := block245W2) (w3 := block245W3) (w4 := block245W4)
    (s1 := block245S1) (s2 := block245S2) (s3 := block245S3) (s4 := block245S4)
    hboxes hcover block245LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block245RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block245RightChunk000 block245W1 block245W2 block245W3 block245W4 block245S1 block245S2 block245S3 block245S4

theorem block245RightChunk000ParamsCertificate_eq_true :
    block245RightChunk000ParamsCertificate = true := by
  native_decide

theorem block245_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block245RightChunk000L : ℝ) (block245RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block245S1 : ℝ))
    (hy2ne : y ≠ (block245S2 : ℝ))
    (hy3ne : y ≠ (block245S3 : ℝ))
    (hy4ne : y ≠ (block245S4 : ℝ)) :
    0 < block245V y := by
  have hcert := block245RightChunk000Certificate_eq_true
  unfold block245RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block245RightChunk000) (lo := block245RightChunk000L) (hi := block245RightChunk000R)
    (w1 := block245W1) (w2 := block245W2) (w3 := block245W3) (w4 := block245W4)
    (s1 := block245S1) (s2 := block245S2) (s3 := block245S3) (s4 := block245S4)
    hboxes hcover block245RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block245RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block245RightChunk001 block245W1 block245W2 block245W3 block245W4 block245S1 block245S2 block245S3 block245S4

theorem block245RightChunk001ParamsCertificate_eq_true :
    block245RightChunk001ParamsCertificate = true := by
  native_decide

theorem block245_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block245RightChunk001L : ℝ) (block245RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block245S1 : ℝ))
    (hy2ne : y ≠ (block245S2 : ℝ))
    (hy3ne : y ≠ (block245S3 : ℝ))
    (hy4ne : y ≠ (block245S4 : ℝ)) :
    0 < block245V y := by
  have hcert := block245RightChunk001Certificate_eq_true
  unfold block245RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block245RightChunk001) (lo := block245RightChunk001L) (hi := block245RightChunk001R)
    (w1 := block245W1) (w2 := block245W2) (w3 := block245W3) (w4 := block245W4)
    (s1 := block245S1) (s2 := block245S2) (s3 := block245S3) (s4 := block245S4)
    hboxes hcover block245RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block245_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block245RightL : ℝ) (block245RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block245S1 : ℝ))
    (hy2ne : y ≠ (block245S2 : ℝ))
    (hy3ne : y ≠ (block245S3 : ℝ))
    (hy4ne : y ≠ (block245S4 : ℝ)) :
    0 < block245V y := by
  by_cases h0 : y ≤ (block245RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block245RightChunk000L : ℝ) (block245RightChunk000R : ℝ) := by
      have hL : (block245RightChunk000L : ℝ) = (block245RightL : ℝ) := by
        norm_num [block245RightChunk000L, block245RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block245_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    have hprev : (block245RightChunk000R : ℝ) < y := lt_of_not_ge h0
    have hL : (block245RightChunk001L : ℝ) = (block245RightChunk000R : ℝ) := by
      norm_num [block245RightChunk001L, block245RightChunk000R]
    have hR : (block245RightChunk001R : ℝ) = (block245RightR : ℝ) := by
      norm_num [block245RightChunk001R, block245RightR]
    have hyc : y ∈ Icc (block245RightChunk001L : ℝ) (block245RightChunk001R : ℝ) := by
      constructor
      · linarith [hprev, hL]
      · linarith [hy.2, hR]
    exact block245_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block245_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block245LeftL : ℝ) (block245LeftR : ℝ) →
    y ≠ 0 → y ≠ (block245S1 : ℝ) → y ≠ (block245S2 : ℝ) →
    y ≠ (block245S3 : ℝ) → y ≠ (block245S4 : ℝ) → 0 < block245V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block245RightL : ℝ) (block245RightR : ℝ) →
    y ≠ 0 → y ≠ (block245S1 : ℝ) → y ≠ (block245S2 : ℝ) →
    y ≠ (block245S3 : ℝ) → y ≠ (block245S4 : ℝ) → 0 < block245V y)

theorem block245_reallog_certificate_proof :
    block245_reallog_certificate := by
  exact ⟨block245_left_V_pos, block245_right_V_pos⟩

end Block245
end M1817475
end Erdos1038Lean
