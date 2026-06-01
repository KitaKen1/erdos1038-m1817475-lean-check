import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block405

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block405

open Set

def block405W1 : Rat := ((459006633687769 : Rat) / 625000000000000)
def block405W2 : Rat := (0 : Rat)
def block405W3 : Rat := ((28128789619630523 : Rat) / 100000000000000000)
def block405W4 : Rat := ((4584671735785227 : Rat) / 50000000000000000)
def block405S1 : Rat := ((18174751 : Rat) / 10000000)
def block405S2 : Rat := ((511587 : Rat) / 200000)
def block405S3 : Rat := ((132216168839285714353 : Rat) / 50000000000000000000)
def block405S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block405V (y : ℝ) : ℝ :=
  ratPotential block405W1 block405W2 block405W3 block405W4 block405S1 block405S2 block405S3 block405S4 y

def block405LeftParamsCertificate : Bool :=
  allBoxesSameParams block405LeftBoxes block405W1 block405W2 block405W3 block405W4 block405S1 block405S2 block405S3 block405S4

theorem block405LeftParamsCertificate_eq_true :
    block405LeftParamsCertificate = true := by
  native_decide

theorem block405_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block405LeftL : ℝ) (block405LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block405S1 : ℝ))
    (hy2ne : y ≠ (block405S2 : ℝ))
    (hy3ne : y ≠ (block405S3 : ℝ))
    (hy4ne : y ≠ (block405S4 : ℝ)) :
    0 < block405V y := by
  have hcert := block405LeftCertificate_eq_true
  unfold block405LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block405LeftBoxes) (lo := block405LeftL) (hi := block405LeftR)
    (w1 := block405W1) (w2 := block405W2) (w3 := block405W3) (w4 := block405W4)
    (s1 := block405S1) (s2 := block405S2) (s3 := block405S3) (s4 := block405S4)
    hboxes hcover block405LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block405RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block405RightChunk000 block405W1 block405W2 block405W3 block405W4 block405S1 block405S2 block405S3 block405S4

theorem block405RightChunk000ParamsCertificate_eq_true :
    block405RightChunk000ParamsCertificate = true := by
  native_decide

theorem block405_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block405RightChunk000L : ℝ) (block405RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block405S1 : ℝ))
    (hy2ne : y ≠ (block405S2 : ℝ))
    (hy3ne : y ≠ (block405S3 : ℝ))
    (hy4ne : y ≠ (block405S4 : ℝ)) :
    0 < block405V y := by
  have hcert := block405RightChunk000Certificate_eq_true
  unfold block405RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block405RightChunk000) (lo := block405RightChunk000L) (hi := block405RightChunk000R)
    (w1 := block405W1) (w2 := block405W2) (w3 := block405W3) (w4 := block405W4)
    (s1 := block405S1) (s2 := block405S2) (s3 := block405S3) (s4 := block405S4)
    hboxes hcover block405RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block405RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block405RightChunk001 block405W1 block405W2 block405W3 block405W4 block405S1 block405S2 block405S3 block405S4

theorem block405RightChunk001ParamsCertificate_eq_true :
    block405RightChunk001ParamsCertificate = true := by
  native_decide

theorem block405_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block405RightChunk001L : ℝ) (block405RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block405S1 : ℝ))
    (hy2ne : y ≠ (block405S2 : ℝ))
    (hy3ne : y ≠ (block405S3 : ℝ))
    (hy4ne : y ≠ (block405S4 : ℝ)) :
    0 < block405V y := by
  have hcert := block405RightChunk001Certificate_eq_true
  unfold block405RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block405RightChunk001) (lo := block405RightChunk001L) (hi := block405RightChunk001R)
    (w1 := block405W1) (w2 := block405W2) (w3 := block405W3) (w4 := block405W4)
    (s1 := block405S1) (s2 := block405S2) (s3 := block405S3) (s4 := block405S4)
    hboxes hcover block405RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block405_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block405RightL : ℝ) (block405RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block405S1 : ℝ))
    (hy2ne : y ≠ (block405S2 : ℝ))
    (hy3ne : y ≠ (block405S3 : ℝ))
    (hy4ne : y ≠ (block405S4 : ℝ)) :
    0 < block405V y := by
  by_cases h0 : y ≤ (block405RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block405RightChunk000L : ℝ) (block405RightChunk000R : ℝ) := by
      have hL : (block405RightChunk000L : ℝ) = (block405RightL : ℝ) := by
        norm_num [block405RightChunk000L, block405RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block405_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    have hprev : (block405RightChunk000R : ℝ) < y := lt_of_not_ge h0
    have hL : (block405RightChunk001L : ℝ) = (block405RightChunk000R : ℝ) := by
      norm_num [block405RightChunk001L, block405RightChunk000R]
    have hR : (block405RightChunk001R : ℝ) = (block405RightR : ℝ) := by
      norm_num [block405RightChunk001R, block405RightR]
    have hyc : y ∈ Icc (block405RightChunk001L : ℝ) (block405RightChunk001R : ℝ) := by
      constructor
      · linarith [hprev, hL]
      · linarith [hy.2, hR]
    exact block405_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block405_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block405LeftL : ℝ) (block405LeftR : ℝ) →
    y ≠ 0 → y ≠ (block405S1 : ℝ) → y ≠ (block405S2 : ℝ) →
    y ≠ (block405S3 : ℝ) → y ≠ (block405S4 : ℝ) → 0 < block405V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block405RightL : ℝ) (block405RightR : ℝ) →
    y ≠ 0 → y ≠ (block405S1 : ℝ) → y ≠ (block405S2 : ℝ) →
    y ≠ (block405S3 : ℝ) → y ≠ (block405S4 : ℝ) → 0 < block405V y)

theorem block405_reallog_certificate_proof :
    block405_reallog_certificate := by
  exact ⟨block405_left_V_pos, block405_right_V_pos⟩

end Block405
end M1817475
end Erdos1038Lean
