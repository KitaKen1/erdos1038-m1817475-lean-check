import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block000

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block000

open Set

def block000W1 : Rat := ((22270102833143817 : Rat) / 10000000000000000)
def block000W2 : Rat := (0 : Rat)
def block000W3 : Rat := (0 : Rat)
def block000W4 : Rat := ((5906017035486959 : Rat) / 20000000000000000)
def block000S1 : Rat := ((18174751 : Rat) / 10000000)
def block000S2 : Rat := ((511587 : Rat) / 200000)
def block000S3 : Rat := ((107000619 : Rat) / 40000000)
def block000S4 : Rat := ((17422615200892856517 : Rat) / 6250000000000000000)

noncomputable def block000V (y : ℝ) : ℝ :=
  ratPotential block000W1 block000W2 block000W3 block000W4 block000S1 block000S2 block000S3 block000S4 y

def block000LeftParamsCertificate : Bool :=
  allBoxesSameParams block000LeftBoxes block000W1 block000W2 block000W3 block000W4 block000S1 block000S2 block000S3 block000S4

theorem block000LeftParamsCertificate_eq_true :
    block000LeftParamsCertificate = true := by
  native_decide

theorem block000_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block000LeftL : ℝ) (block000LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block000S1 : ℝ))
    (hy2ne : y ≠ (block000S2 : ℝ))
    (hy3ne : y ≠ (block000S3 : ℝ))
    (hy4ne : y ≠ (block000S4 : ℝ)) :
    0 < block000V y := by
  have hcert := block000LeftCertificate_eq_true
  unfold block000LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block000LeftBoxes) (lo := block000LeftL) (hi := block000LeftR)
    (w1 := block000W1) (w2 := block000W2) (w3 := block000W3) (w4 := block000W4)
    (s1 := block000S1) (s2 := block000S2) (s3 := block000S3) (s4 := block000S4)
    hboxes hcover block000LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block000RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block000RightChunk000 block000W1 block000W2 block000W3 block000W4 block000S1 block000S2 block000S3 block000S4

theorem block000RightChunk000ParamsCertificate_eq_true :
    block000RightChunk000ParamsCertificate = true := by
  native_decide

theorem block000_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block000RightChunk000L : ℝ) (block000RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block000S1 : ℝ))
    (hy2ne : y ≠ (block000S2 : ℝ))
    (hy3ne : y ≠ (block000S3 : ℝ))
    (hy4ne : y ≠ (block000S4 : ℝ)) :
    0 < block000V y := by
  have hcert := block000RightChunk000Certificate_eq_true
  unfold block000RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block000RightChunk000) (lo := block000RightChunk000L) (hi := block000RightChunk000R)
    (w1 := block000W1) (w2 := block000W2) (w3 := block000W3) (w4 := block000W4)
    (s1 := block000S1) (s2 := block000S2) (s3 := block000S3) (s4 := block000S4)
    hboxes hcover block000RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block000RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block000RightChunk001 block000W1 block000W2 block000W3 block000W4 block000S1 block000S2 block000S3 block000S4

theorem block000RightChunk001ParamsCertificate_eq_true :
    block000RightChunk001ParamsCertificate = true := by
  native_decide

theorem block000_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block000RightChunk001L : ℝ) (block000RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block000S1 : ℝ))
    (hy2ne : y ≠ (block000S2 : ℝ))
    (hy3ne : y ≠ (block000S3 : ℝ))
    (hy4ne : y ≠ (block000S4 : ℝ)) :
    0 < block000V y := by
  have hcert := block000RightChunk001Certificate_eq_true
  unfold block000RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block000RightChunk001) (lo := block000RightChunk001L) (hi := block000RightChunk001R)
    (w1 := block000W1) (w2 := block000W2) (w3 := block000W3) (w4 := block000W4)
    (s1 := block000S1) (s2 := block000S2) (s3 := block000S3) (s4 := block000S4)
    hboxes hcover block000RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block000_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block000RightL : ℝ) (block000RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block000S1 : ℝ))
    (hy2ne : y ≠ (block000S2 : ℝ))
    (hy3ne : y ≠ (block000S3 : ℝ))
    (hy4ne : y ≠ (block000S4 : ℝ)) :
    0 < block000V y := by
  by_cases h0 : y ≤ (block000RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block000RightChunk000L : ℝ) (block000RightChunk000R : ℝ) := by
      have hL : (block000RightChunk000L : ℝ) = (block000RightL : ℝ) := by
        norm_num [block000RightChunk000L, block000RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block000_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    have hprev : (block000RightChunk000R : ℝ) < y := lt_of_not_ge h0
    have hL : (block000RightChunk001L : ℝ) = (block000RightChunk000R : ℝ) := by
      norm_num [block000RightChunk001L, block000RightChunk000R]
    have hR : (block000RightChunk001R : ℝ) = (block000RightR : ℝ) := by
      norm_num [block000RightChunk001R, block000RightR]
    have hyc : y ∈ Icc (block000RightChunk001L : ℝ) (block000RightChunk001R : ℝ) := by
      constructor
      · linarith [hprev, hL]
      · linarith [hy.2, hR]
    exact block000_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block000_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block000LeftL : ℝ) (block000LeftR : ℝ) →
    y ≠ 0 → y ≠ (block000S1 : ℝ) → y ≠ (block000S2 : ℝ) →
    y ≠ (block000S3 : ℝ) → y ≠ (block000S4 : ℝ) → 0 < block000V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block000RightL : ℝ) (block000RightR : ℝ) →
    y ≠ 0 → y ≠ (block000S1 : ℝ) → y ≠ (block000S2 : ℝ) →
    y ≠ (block000S3 : ℝ) → y ≠ (block000S4 : ℝ) → 0 < block000V y)

theorem block000_reallog_certificate_proof :
    block000_reallog_certificate := by
  exact ⟨block000_left_V_pos, block000_right_V_pos⟩

end Block000
end M1817475
end Erdos1038Lean
