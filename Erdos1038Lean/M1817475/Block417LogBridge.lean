import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block417

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block417

open Set

def block417W1 : Rat := ((3480112901166697 : Rat) / 5000000000000000)
def block417W2 : Rat := (0 : Rat)
def block417W3 : Rat := ((734021554533117 : Rat) / 2500000000000000)
def block417W4 : Rat := ((431863091002331 : Rat) / 5000000000000000)
def block417S1 : Rat := ((18174751 : Rat) / 10000000)
def block417S2 : Rat := ((511587 : Rat) / 200000)
def block417S3 : Rat := ((131981579553571428649 : Rat) / 50000000000000000000)
def block417S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block417V (y : ℝ) : ℝ :=
  ratPotential block417W1 block417W2 block417W3 block417W4 block417S1 block417S2 block417S3 block417S4 y

def block417LeftParamsCertificate : Bool :=
  allBoxesSameParams block417LeftBoxes block417W1 block417W2 block417W3 block417W4 block417S1 block417S2 block417S3 block417S4

theorem block417LeftParamsCertificate_eq_true :
    block417LeftParamsCertificate = true := by
  native_decide

theorem block417_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block417LeftL : ℝ) (block417LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block417S1 : ℝ))
    (hy2ne : y ≠ (block417S2 : ℝ))
    (hy3ne : y ≠ (block417S3 : ℝ))
    (hy4ne : y ≠ (block417S4 : ℝ)) :
    0 < block417V y := by
  have hcert := block417LeftCertificate_eq_true
  unfold block417LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block417LeftBoxes) (lo := block417LeftL) (hi := block417LeftR)
    (w1 := block417W1) (w2 := block417W2) (w3 := block417W3) (w4 := block417W4)
    (s1 := block417S1) (s2 := block417S2) (s3 := block417S3) (s4 := block417S4)
    hboxes hcover block417LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block417RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block417RightChunk000 block417W1 block417W2 block417W3 block417W4 block417S1 block417S2 block417S3 block417S4

theorem block417RightChunk000ParamsCertificate_eq_true :
    block417RightChunk000ParamsCertificate = true := by
  native_decide

theorem block417_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block417RightChunk000L : ℝ) (block417RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block417S1 : ℝ))
    (hy2ne : y ≠ (block417S2 : ℝ))
    (hy3ne : y ≠ (block417S3 : ℝ))
    (hy4ne : y ≠ (block417S4 : ℝ)) :
    0 < block417V y := by
  have hcert := block417RightChunk000Certificate_eq_true
  unfold block417RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block417RightChunk000) (lo := block417RightChunk000L) (hi := block417RightChunk000R)
    (w1 := block417W1) (w2 := block417W2) (w3 := block417W3) (w4 := block417W4)
    (s1 := block417S1) (s2 := block417S2) (s3 := block417S3) (s4 := block417S4)
    hboxes hcover block417RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block417RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block417RightChunk001 block417W1 block417W2 block417W3 block417W4 block417S1 block417S2 block417S3 block417S4

theorem block417RightChunk001ParamsCertificate_eq_true :
    block417RightChunk001ParamsCertificate = true := by
  native_decide

theorem block417_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block417RightChunk001L : ℝ) (block417RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block417S1 : ℝ))
    (hy2ne : y ≠ (block417S2 : ℝ))
    (hy3ne : y ≠ (block417S3 : ℝ))
    (hy4ne : y ≠ (block417S4 : ℝ)) :
    0 < block417V y := by
  have hcert := block417RightChunk001Certificate_eq_true
  unfold block417RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block417RightChunk001) (lo := block417RightChunk001L) (hi := block417RightChunk001R)
    (w1 := block417W1) (w2 := block417W2) (w3 := block417W3) (w4 := block417W4)
    (s1 := block417S1) (s2 := block417S2) (s3 := block417S3) (s4 := block417S4)
    hboxes hcover block417RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block417_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block417RightL : ℝ) (block417RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block417S1 : ℝ))
    (hy2ne : y ≠ (block417S2 : ℝ))
    (hy3ne : y ≠ (block417S3 : ℝ))
    (hy4ne : y ≠ (block417S4 : ℝ)) :
    0 < block417V y := by
  by_cases h0 : y ≤ (block417RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block417RightChunk000L : ℝ) (block417RightChunk000R : ℝ) := by
      have hL : (block417RightChunk000L : ℝ) = (block417RightL : ℝ) := by
        norm_num [block417RightChunk000L, block417RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block417_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    have hprev : (block417RightChunk000R : ℝ) < y := lt_of_not_ge h0
    have hL : (block417RightChunk001L : ℝ) = (block417RightChunk000R : ℝ) := by
      norm_num [block417RightChunk001L, block417RightChunk000R]
    have hR : (block417RightChunk001R : ℝ) = (block417RightR : ℝ) := by
      norm_num [block417RightChunk001R, block417RightR]
    have hyc : y ∈ Icc (block417RightChunk001L : ℝ) (block417RightChunk001R : ℝ) := by
      constructor
      · linarith [hprev, hL]
      · linarith [hy.2, hR]
    exact block417_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block417_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block417LeftL : ℝ) (block417LeftR : ℝ) →
    y ≠ 0 → y ≠ (block417S1 : ℝ) → y ≠ (block417S2 : ℝ) →
    y ≠ (block417S3 : ℝ) → y ≠ (block417S4 : ℝ) → 0 < block417V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block417RightL : ℝ) (block417RightR : ℝ) →
    y ≠ 0 → y ≠ (block417S1 : ℝ) → y ≠ (block417S2 : ℝ) →
    y ≠ (block417S3 : ℝ) → y ≠ (block417S4 : ℝ) → 0 < block417V y)

theorem block417_reallog_certificate_proof :
    block417_reallog_certificate := by
  exact ⟨block417_left_V_pos, block417_right_V_pos⟩

end Block417
end M1817475
end Erdos1038Lean
