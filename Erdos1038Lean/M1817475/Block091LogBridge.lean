import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block091

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block091

open Set

def block091W1 : Rat := ((1462816853022853 : Rat) / 400000000000000)
def block091W2 : Rat := (0 : Rat)
def block091W3 : Rat := (0 : Rat)
def block091W4 : Rat := ((1151845655797093 : Rat) / 5000000000000000)
def block091S1 : Rat := ((18174751 : Rat) / 10000000)
def block091S2 : Rat := ((511587 : Rat) / 200000)
def block091S3 : Rat := ((107000619 : Rat) / 40000000)
def block091S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block091V (y : ℝ) : ℝ :=
  ratPotential block091W1 block091W2 block091W3 block091W4 block091S1 block091S2 block091S3 block091S4 y

def block091LeftParamsCertificate : Bool :=
  allBoxesSameParams block091LeftBoxes block091W1 block091W2 block091W3 block091W4 block091S1 block091S2 block091S3 block091S4

theorem block091LeftParamsCertificate_eq_true :
    block091LeftParamsCertificate = true := by
  native_decide

theorem block091_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block091LeftL : ℝ) (block091LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block091S1 : ℝ))
    (hy2ne : y ≠ (block091S2 : ℝ))
    (hy3ne : y ≠ (block091S3 : ℝ))
    (hy4ne : y ≠ (block091S4 : ℝ)) :
    0 < block091V y := by
  have hcert := block091LeftCertificate_eq_true
  unfold block091LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block091LeftBoxes) (lo := block091LeftL) (hi := block091LeftR)
    (w1 := block091W1) (w2 := block091W2) (w3 := block091W3) (w4 := block091W4)
    (s1 := block091S1) (s2 := block091S2) (s3 := block091S3) (s4 := block091S4)
    hboxes hcover block091LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block091RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block091RightChunk000 block091W1 block091W2 block091W3 block091W4 block091S1 block091S2 block091S3 block091S4

theorem block091RightChunk000ParamsCertificate_eq_true :
    block091RightChunk000ParamsCertificate = true := by
  native_decide

theorem block091_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block091RightChunk000L : ℝ) (block091RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block091S1 : ℝ))
    (hy2ne : y ≠ (block091S2 : ℝ))
    (hy3ne : y ≠ (block091S3 : ℝ))
    (hy4ne : y ≠ (block091S4 : ℝ)) :
    0 < block091V y := by
  have hcert := block091RightChunk000Certificate_eq_true
  unfold block091RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block091RightChunk000) (lo := block091RightChunk000L) (hi := block091RightChunk000R)
    (w1 := block091W1) (w2 := block091W2) (w3 := block091W3) (w4 := block091W4)
    (s1 := block091S1) (s2 := block091S2) (s3 := block091S3) (s4 := block091S4)
    hboxes hcover block091RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block091RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block091RightChunk001 block091W1 block091W2 block091W3 block091W4 block091S1 block091S2 block091S3 block091S4

theorem block091RightChunk001ParamsCertificate_eq_true :
    block091RightChunk001ParamsCertificate = true := by
  native_decide

theorem block091_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block091RightChunk001L : ℝ) (block091RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block091S1 : ℝ))
    (hy2ne : y ≠ (block091S2 : ℝ))
    (hy3ne : y ≠ (block091S3 : ℝ))
    (hy4ne : y ≠ (block091S4 : ℝ)) :
    0 < block091V y := by
  have hcert := block091RightChunk001Certificate_eq_true
  unfold block091RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block091RightChunk001) (lo := block091RightChunk001L) (hi := block091RightChunk001R)
    (w1 := block091W1) (w2 := block091W2) (w3 := block091W3) (w4 := block091W4)
    (s1 := block091S1) (s2 := block091S2) (s3 := block091S3) (s4 := block091S4)
    hboxes hcover block091RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block091_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block091RightL : ℝ) (block091RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block091S1 : ℝ))
    (hy2ne : y ≠ (block091S2 : ℝ))
    (hy3ne : y ≠ (block091S3 : ℝ))
    (hy4ne : y ≠ (block091S4 : ℝ)) :
    0 < block091V y := by
  by_cases h0 : y ≤ (block091RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block091RightChunk000L : ℝ) (block091RightChunk000R : ℝ) := by
      have hL : (block091RightChunk000L : ℝ) = (block091RightL : ℝ) := by
        norm_num [block091RightChunk000L, block091RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block091_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    have hprev : (block091RightChunk000R : ℝ) < y := lt_of_not_ge h0
    have hL : (block091RightChunk001L : ℝ) = (block091RightChunk000R : ℝ) := by
      norm_num [block091RightChunk001L, block091RightChunk000R]
    have hR : (block091RightChunk001R : ℝ) = (block091RightR : ℝ) := by
      norm_num [block091RightChunk001R, block091RightR]
    have hyc : y ∈ Icc (block091RightChunk001L : ℝ) (block091RightChunk001R : ℝ) := by
      constructor
      · linarith [hprev, hL]
      · linarith [hy.2, hR]
    exact block091_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block091_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block091LeftL : ℝ) (block091LeftR : ℝ) →
    y ≠ 0 → y ≠ (block091S1 : ℝ) → y ≠ (block091S2 : ℝ) →
    y ≠ (block091S3 : ℝ) → y ≠ (block091S4 : ℝ) → 0 < block091V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block091RightL : ℝ) (block091RightR : ℝ) →
    y ≠ 0 → y ≠ (block091S1 : ℝ) → y ≠ (block091S2 : ℝ) →
    y ≠ (block091S3 : ℝ) → y ≠ (block091S4 : ℝ) → 0 < block091V y)

theorem block091_reallog_certificate_proof :
    block091_reallog_certificate := by
  exact ⟨block091_left_V_pos, block091_right_V_pos⟩

end Block091
end M1817475
end Erdos1038Lean
