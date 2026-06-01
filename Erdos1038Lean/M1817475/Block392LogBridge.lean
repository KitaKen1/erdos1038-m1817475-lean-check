import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block392

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block392

open Set

def block392W1 : Rat := ((4017998603018007 : Rat) / 5000000000000000)
def block392W2 : Rat := ((10265692108992001 : Rat) / 250000000000000000)
def block392W3 : Rat := ((1716705266326877 : Rat) / 10000000000000000)
def block392W4 : Rat := ((364775151294377 : Rat) / 2500000000000000)
def block392S1 : Rat := ((18174751 : Rat) / 10000000)
def block392S2 : Rat := ((511587 : Rat) / 200000)
def block392S3 : Rat := ((132470307232142857199 : Rat) / 50000000000000000000)
def block392S4 : Rat := ((34776808526785713037 : Rat) / 12500000000000000000)

noncomputable def block392V (y : ℝ) : ℝ :=
  ratPotential block392W1 block392W2 block392W3 block392W4 block392S1 block392S2 block392S3 block392S4 y

def block392LeftParamsCertificate : Bool :=
  allBoxesSameParams block392LeftBoxes block392W1 block392W2 block392W3 block392W4 block392S1 block392S2 block392S3 block392S4

theorem block392LeftParamsCertificate_eq_true :
    block392LeftParamsCertificate = true := by
  native_decide

theorem block392_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block392LeftL : ℝ) (block392LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block392S1 : ℝ))
    (hy2ne : y ≠ (block392S2 : ℝ))
    (hy3ne : y ≠ (block392S3 : ℝ))
    (hy4ne : y ≠ (block392S4 : ℝ)) :
    0 < block392V y := by
  have hcert := block392LeftCertificate_eq_true
  unfold block392LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block392LeftBoxes) (lo := block392LeftL) (hi := block392LeftR)
    (w1 := block392W1) (w2 := block392W2) (w3 := block392W3) (w4 := block392W4)
    (s1 := block392S1) (s2 := block392S2) (s3 := block392S3) (s4 := block392S4)
    hboxes hcover block392LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block392RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block392RightChunk000 block392W1 block392W2 block392W3 block392W4 block392S1 block392S2 block392S3 block392S4

theorem block392RightChunk000ParamsCertificate_eq_true :
    block392RightChunk000ParamsCertificate = true := by
  native_decide

theorem block392_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block392RightChunk000L : ℝ) (block392RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block392S1 : ℝ))
    (hy2ne : y ≠ (block392S2 : ℝ))
    (hy3ne : y ≠ (block392S3 : ℝ))
    (hy4ne : y ≠ (block392S4 : ℝ)) :
    0 < block392V y := by
  have hcert := block392RightChunk000Certificate_eq_true
  unfold block392RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block392RightChunk000) (lo := block392RightChunk000L) (hi := block392RightChunk000R)
    (w1 := block392W1) (w2 := block392W2) (w3 := block392W3) (w4 := block392W4)
    (s1 := block392S1) (s2 := block392S2) (s3 := block392S3) (s4 := block392S4)
    hboxes hcover block392RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block392RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block392RightChunk001 block392W1 block392W2 block392W3 block392W4 block392S1 block392S2 block392S3 block392S4

theorem block392RightChunk001ParamsCertificate_eq_true :
    block392RightChunk001ParamsCertificate = true := by
  native_decide

theorem block392_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block392RightChunk001L : ℝ) (block392RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block392S1 : ℝ))
    (hy2ne : y ≠ (block392S2 : ℝ))
    (hy3ne : y ≠ (block392S3 : ℝ))
    (hy4ne : y ≠ (block392S4 : ℝ)) :
    0 < block392V y := by
  have hcert := block392RightChunk001Certificate_eq_true
  unfold block392RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block392RightChunk001) (lo := block392RightChunk001L) (hi := block392RightChunk001R)
    (w1 := block392W1) (w2 := block392W2) (w3 := block392W3) (w4 := block392W4)
    (s1 := block392S1) (s2 := block392S2) (s3 := block392S3) (s4 := block392S4)
    hboxes hcover block392RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block392_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block392RightL : ℝ) (block392RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block392S1 : ℝ))
    (hy2ne : y ≠ (block392S2 : ℝ))
    (hy3ne : y ≠ (block392S3 : ℝ))
    (hy4ne : y ≠ (block392S4 : ℝ)) :
    0 < block392V y := by
  by_cases h0 : y ≤ (block392RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block392RightChunk000L : ℝ) (block392RightChunk000R : ℝ) := by
      have hL : (block392RightChunk000L : ℝ) = (block392RightL : ℝ) := by
        norm_num [block392RightChunk000L, block392RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block392_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    have hprev : (block392RightChunk000R : ℝ) < y := lt_of_not_ge h0
    have hL : (block392RightChunk001L : ℝ) = (block392RightChunk000R : ℝ) := by
      norm_num [block392RightChunk001L, block392RightChunk000R]
    have hR : (block392RightChunk001R : ℝ) = (block392RightR : ℝ) := by
      norm_num [block392RightChunk001R, block392RightR]
    have hyc : y ∈ Icc (block392RightChunk001L : ℝ) (block392RightChunk001R : ℝ) := by
      constructor
      · linarith [hprev, hL]
      · linarith [hy.2, hR]
    exact block392_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block392_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block392LeftL : ℝ) (block392LeftR : ℝ) →
    y ≠ 0 → y ≠ (block392S1 : ℝ) → y ≠ (block392S2 : ℝ) →
    y ≠ (block392S3 : ℝ) → y ≠ (block392S4 : ℝ) → 0 < block392V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block392RightL : ℝ) (block392RightR : ℝ) →
    y ≠ 0 → y ≠ (block392S1 : ℝ) → y ≠ (block392S2 : ℝ) →
    y ≠ (block392S3 : ℝ) → y ≠ (block392S4 : ℝ) → 0 < block392V y)

theorem block392_reallog_certificate_proof :
    block392_reallog_certificate := by
  exact ⟨block392_left_V_pos, block392_right_V_pos⟩

end Block392
end M1817475
end Erdos1038Lean
