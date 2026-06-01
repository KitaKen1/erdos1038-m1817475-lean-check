import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block246

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block246

open Set

def block246W1 : Rat := ((8565624676365671 : Rat) / 10000000000000000)
def block246W2 : Rat := ((4311557324172479 : Rat) / 50000000000000000)
def block246W3 : Rat := ((2179614625968103 : Rat) / 50000000000000000)
def block246W4 : Rat := ((4136158747197829 : Rat) / 20000000000000000)
def block246S1 : Rat := ((18174751 : Rat) / 10000000)
def block246S2 : Rat := ((511587 : Rat) / 200000)
def block246S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block246S4 : Rat := ((3421965897321428449 : Rat) / 1250000000000000000)

noncomputable def block246V (y : ℝ) : ℝ :=
  ratPotential block246W1 block246W2 block246W3 block246W4 block246S1 block246S2 block246S3 block246S4 y

def block246LeftParamsCertificate : Bool :=
  allBoxesSameParams block246LeftBoxes block246W1 block246W2 block246W3 block246W4 block246S1 block246S2 block246S3 block246S4

theorem block246LeftParamsCertificate_eq_true :
    block246LeftParamsCertificate = true := by
  native_decide

theorem block246_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block246LeftL : ℝ) (block246LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block246S1 : ℝ))
    (hy2ne : y ≠ (block246S2 : ℝ))
    (hy3ne : y ≠ (block246S3 : ℝ))
    (hy4ne : y ≠ (block246S4 : ℝ)) :
    0 < block246V y := by
  have hcert := block246LeftCertificate_eq_true
  unfold block246LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block246LeftBoxes) (lo := block246LeftL) (hi := block246LeftR)
    (w1 := block246W1) (w2 := block246W2) (w3 := block246W3) (w4 := block246W4)
    (s1 := block246S1) (s2 := block246S2) (s3 := block246S3) (s4 := block246S4)
    hboxes hcover block246LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block246RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block246RightChunk000 block246W1 block246W2 block246W3 block246W4 block246S1 block246S2 block246S3 block246S4

theorem block246RightChunk000ParamsCertificate_eq_true :
    block246RightChunk000ParamsCertificate = true := by
  native_decide

theorem block246_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block246RightChunk000L : ℝ) (block246RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block246S1 : ℝ))
    (hy2ne : y ≠ (block246S2 : ℝ))
    (hy3ne : y ≠ (block246S3 : ℝ))
    (hy4ne : y ≠ (block246S4 : ℝ)) :
    0 < block246V y := by
  have hcert := block246RightChunk000Certificate_eq_true
  unfold block246RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block246RightChunk000) (lo := block246RightChunk000L) (hi := block246RightChunk000R)
    (w1 := block246W1) (w2 := block246W2) (w3 := block246W3) (w4 := block246W4)
    (s1 := block246S1) (s2 := block246S2) (s3 := block246S3) (s4 := block246S4)
    hboxes hcover block246RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block246RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block246RightChunk001 block246W1 block246W2 block246W3 block246W4 block246S1 block246S2 block246S3 block246S4

theorem block246RightChunk001ParamsCertificate_eq_true :
    block246RightChunk001ParamsCertificate = true := by
  native_decide

theorem block246_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block246RightChunk001L : ℝ) (block246RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block246S1 : ℝ))
    (hy2ne : y ≠ (block246S2 : ℝ))
    (hy3ne : y ≠ (block246S3 : ℝ))
    (hy4ne : y ≠ (block246S4 : ℝ)) :
    0 < block246V y := by
  have hcert := block246RightChunk001Certificate_eq_true
  unfold block246RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block246RightChunk001) (lo := block246RightChunk001L) (hi := block246RightChunk001R)
    (w1 := block246W1) (w2 := block246W2) (w3 := block246W3) (w4 := block246W4)
    (s1 := block246S1) (s2 := block246S2) (s3 := block246S3) (s4 := block246S4)
    hboxes hcover block246RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block246_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block246RightL : ℝ) (block246RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block246S1 : ℝ))
    (hy2ne : y ≠ (block246S2 : ℝ))
    (hy3ne : y ≠ (block246S3 : ℝ))
    (hy4ne : y ≠ (block246S4 : ℝ)) :
    0 < block246V y := by
  by_cases h0 : y ≤ (block246RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block246RightChunk000L : ℝ) (block246RightChunk000R : ℝ) := by
      have hL : (block246RightChunk000L : ℝ) = (block246RightL : ℝ) := by
        norm_num [block246RightChunk000L, block246RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block246_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    have hprev : (block246RightChunk000R : ℝ) < y := lt_of_not_ge h0
    have hL : (block246RightChunk001L : ℝ) = (block246RightChunk000R : ℝ) := by
      norm_num [block246RightChunk001L, block246RightChunk000R]
    have hR : (block246RightChunk001R : ℝ) = (block246RightR : ℝ) := by
      norm_num [block246RightChunk001R, block246RightR]
    have hyc : y ∈ Icc (block246RightChunk001L : ℝ) (block246RightChunk001R : ℝ) := by
      constructor
      · linarith [hprev, hL]
      · linarith [hy.2, hR]
    exact block246_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block246_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block246LeftL : ℝ) (block246LeftR : ℝ) →
    y ≠ 0 → y ≠ (block246S1 : ℝ) → y ≠ (block246S2 : ℝ) →
    y ≠ (block246S3 : ℝ) → y ≠ (block246S4 : ℝ) → 0 < block246V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block246RightL : ℝ) (block246RightR : ℝ) →
    y ≠ 0 → y ≠ (block246S1 : ℝ) → y ≠ (block246S2 : ℝ) →
    y ≠ (block246S3 : ℝ) → y ≠ (block246S4 : ℝ) → 0 < block246V y)

theorem block246_reallog_certificate_proof :
    block246_reallog_certificate := by
  exact ⟨block246_left_V_pos, block246_right_V_pos⟩

end Block246
end M1817475
end Erdos1038Lean
