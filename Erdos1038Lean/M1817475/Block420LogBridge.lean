import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block420

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block420

open Set

def block420W1 : Rat := ((26821854436179 : Rat) / 39062500000000)
def block420W2 : Rat := (0 : Rat)
def block420W3 : Rat := ((14842657010346613 : Rat) / 50000000000000000)
def block420W4 : Rat := ((4245326646780629 : Rat) / 50000000000000000)
def block420S1 : Rat := ((18174751 : Rat) / 10000000)
def block420S2 : Rat := ((511587 : Rat) / 200000)
def block420S3 : Rat := ((131922932232142857223 : Rat) / 50000000000000000000)
def block420S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block420V (y : ℝ) : ℝ :=
  ratPotential block420W1 block420W2 block420W3 block420W4 block420S1 block420S2 block420S3 block420S4 y

def block420LeftParamsCertificate : Bool :=
  allBoxesSameParams block420LeftBoxes block420W1 block420W2 block420W3 block420W4 block420S1 block420S2 block420S3 block420S4

theorem block420LeftParamsCertificate_eq_true :
    block420LeftParamsCertificate = true := by
  native_decide

theorem block420_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block420LeftL : ℝ) (block420LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block420S1 : ℝ))
    (hy2ne : y ≠ (block420S2 : ℝ))
    (hy3ne : y ≠ (block420S3 : ℝ))
    (hy4ne : y ≠ (block420S4 : ℝ)) :
    0 < block420V y := by
  have hcert := block420LeftCertificate_eq_true
  unfold block420LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block420LeftBoxes) (lo := block420LeftL) (hi := block420LeftR)
    (w1 := block420W1) (w2 := block420W2) (w3 := block420W3) (w4 := block420W4)
    (s1 := block420S1) (s2 := block420S2) (s3 := block420S3) (s4 := block420S4)
    hboxes hcover block420LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block420RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block420RightChunk000 block420W1 block420W2 block420W3 block420W4 block420S1 block420S2 block420S3 block420S4

theorem block420RightChunk000ParamsCertificate_eq_true :
    block420RightChunk000ParamsCertificate = true := by
  native_decide

theorem block420_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block420RightChunk000L : ℝ) (block420RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block420S1 : ℝ))
    (hy2ne : y ≠ (block420S2 : ℝ))
    (hy3ne : y ≠ (block420S3 : ℝ))
    (hy4ne : y ≠ (block420S4 : ℝ)) :
    0 < block420V y := by
  have hcert := block420RightChunk000Certificate_eq_true
  unfold block420RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block420RightChunk000) (lo := block420RightChunk000L) (hi := block420RightChunk000R)
    (w1 := block420W1) (w2 := block420W2) (w3 := block420W3) (w4 := block420W4)
    (s1 := block420S1) (s2 := block420S2) (s3 := block420S3) (s4 := block420S4)
    hboxes hcover block420RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block420RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block420RightChunk001 block420W1 block420W2 block420W3 block420W4 block420S1 block420S2 block420S3 block420S4

theorem block420RightChunk001ParamsCertificate_eq_true :
    block420RightChunk001ParamsCertificate = true := by
  native_decide

theorem block420_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block420RightChunk001L : ℝ) (block420RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block420S1 : ℝ))
    (hy2ne : y ≠ (block420S2 : ℝ))
    (hy3ne : y ≠ (block420S3 : ℝ))
    (hy4ne : y ≠ (block420S4 : ℝ)) :
    0 < block420V y := by
  have hcert := block420RightChunk001Certificate_eq_true
  unfold block420RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block420RightChunk001) (lo := block420RightChunk001L) (hi := block420RightChunk001R)
    (w1 := block420W1) (w2 := block420W2) (w3 := block420W3) (w4 := block420W4)
    (s1 := block420S1) (s2 := block420S2) (s3 := block420S3) (s4 := block420S4)
    hboxes hcover block420RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block420_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block420RightL : ℝ) (block420RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block420S1 : ℝ))
    (hy2ne : y ≠ (block420S2 : ℝ))
    (hy3ne : y ≠ (block420S3 : ℝ))
    (hy4ne : y ≠ (block420S4 : ℝ)) :
    0 < block420V y := by
  by_cases h0 : y ≤ (block420RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block420RightChunk000L : ℝ) (block420RightChunk000R : ℝ) := by
      have hL : (block420RightChunk000L : ℝ) = (block420RightL : ℝ) := by
        norm_num [block420RightChunk000L, block420RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block420_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    have hprev : (block420RightChunk000R : ℝ) < y := lt_of_not_ge h0
    have hL : (block420RightChunk001L : ℝ) = (block420RightChunk000R : ℝ) := by
      norm_num [block420RightChunk001L, block420RightChunk000R]
    have hR : (block420RightChunk001R : ℝ) = (block420RightR : ℝ) := by
      norm_num [block420RightChunk001R, block420RightR]
    have hyc : y ∈ Icc (block420RightChunk001L : ℝ) (block420RightChunk001R : ℝ) := by
      constructor
      · linarith [hprev, hL]
      · linarith [hy.2, hR]
    exact block420_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block420_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block420LeftL : ℝ) (block420LeftR : ℝ) →
    y ≠ 0 → y ≠ (block420S1 : ℝ) → y ≠ (block420S2 : ℝ) →
    y ≠ (block420S3 : ℝ) → y ≠ (block420S4 : ℝ) → 0 < block420V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block420RightL : ℝ) (block420RightR : ℝ) →
    y ≠ 0 → y ≠ (block420S1 : ℝ) → y ≠ (block420S2 : ℝ) →
    y ≠ (block420S3 : ℝ) → y ≠ (block420S4 : ℝ) → 0 < block420V y)

theorem block420_reallog_certificate_proof :
    block420_reallog_certificate := by
  exact ⟨block420_left_V_pos, block420_right_V_pos⟩

end Block420
end M1817475
end Erdos1038Lean
