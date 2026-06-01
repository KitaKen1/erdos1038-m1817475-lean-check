import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block410

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block410

open Set

def block410W1 : Rat := ((448837964396453 : Rat) / 625000000000000)
def block410W2 : Rat := (0 : Rat)
def block410W3 : Rat := ((286361911058809 : Rat) / 1000000000000000)
def block410W4 : Rat := ((8953234796468297 : Rat) / 100000000000000000)
def block410S1 : Rat := ((18174751 : Rat) / 10000000)
def block410S2 : Rat := ((511587 : Rat) / 200000)
def block410S3 : Rat := ((132118423303571428643 : Rat) / 50000000000000000000)
def block410S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block410V (y : ℝ) : ℝ :=
  ratPotential block410W1 block410W2 block410W3 block410W4 block410S1 block410S2 block410S3 block410S4 y

def block410LeftParamsCertificate : Bool :=
  allBoxesSameParams block410LeftBoxes block410W1 block410W2 block410W3 block410W4 block410S1 block410S2 block410S3 block410S4

theorem block410LeftParamsCertificate_eq_true :
    block410LeftParamsCertificate = true := by
  native_decide

theorem block410_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block410LeftL : ℝ) (block410LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block410S1 : ℝ))
    (hy2ne : y ≠ (block410S2 : ℝ))
    (hy3ne : y ≠ (block410S3 : ℝ))
    (hy4ne : y ≠ (block410S4 : ℝ)) :
    0 < block410V y := by
  have hcert := block410LeftCertificate_eq_true
  unfold block410LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block410LeftBoxes) (lo := block410LeftL) (hi := block410LeftR)
    (w1 := block410W1) (w2 := block410W2) (w3 := block410W3) (w4 := block410W4)
    (s1 := block410S1) (s2 := block410S2) (s3 := block410S3) (s4 := block410S4)
    hboxes hcover block410LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block410RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block410RightChunk000 block410W1 block410W2 block410W3 block410W4 block410S1 block410S2 block410S3 block410S4

theorem block410RightChunk000ParamsCertificate_eq_true :
    block410RightChunk000ParamsCertificate = true := by
  native_decide

theorem block410_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block410RightChunk000L : ℝ) (block410RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block410S1 : ℝ))
    (hy2ne : y ≠ (block410S2 : ℝ))
    (hy3ne : y ≠ (block410S3 : ℝ))
    (hy4ne : y ≠ (block410S4 : ℝ)) :
    0 < block410V y := by
  have hcert := block410RightChunk000Certificate_eq_true
  unfold block410RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block410RightChunk000) (lo := block410RightChunk000L) (hi := block410RightChunk000R)
    (w1 := block410W1) (w2 := block410W2) (w3 := block410W3) (w4 := block410W4)
    (s1 := block410S1) (s2 := block410S2) (s3 := block410S3) (s4 := block410S4)
    hboxes hcover block410RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block410RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block410RightChunk001 block410W1 block410W2 block410W3 block410W4 block410S1 block410S2 block410S3 block410S4

theorem block410RightChunk001ParamsCertificate_eq_true :
    block410RightChunk001ParamsCertificate = true := by
  native_decide

theorem block410_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block410RightChunk001L : ℝ) (block410RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block410S1 : ℝ))
    (hy2ne : y ≠ (block410S2 : ℝ))
    (hy3ne : y ≠ (block410S3 : ℝ))
    (hy4ne : y ≠ (block410S4 : ℝ)) :
    0 < block410V y := by
  have hcert := block410RightChunk001Certificate_eq_true
  unfold block410RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block410RightChunk001) (lo := block410RightChunk001L) (hi := block410RightChunk001R)
    (w1 := block410W1) (w2 := block410W2) (w3 := block410W3) (w4 := block410W4)
    (s1 := block410S1) (s2 := block410S2) (s3 := block410S3) (s4 := block410S4)
    hboxes hcover block410RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block410_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block410RightL : ℝ) (block410RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block410S1 : ℝ))
    (hy2ne : y ≠ (block410S2 : ℝ))
    (hy3ne : y ≠ (block410S3 : ℝ))
    (hy4ne : y ≠ (block410S4 : ℝ)) :
    0 < block410V y := by
  by_cases h0 : y ≤ (block410RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block410RightChunk000L : ℝ) (block410RightChunk000R : ℝ) := by
      have hL : (block410RightChunk000L : ℝ) = (block410RightL : ℝ) := by
        norm_num [block410RightChunk000L, block410RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block410_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    have hprev : (block410RightChunk000R : ℝ) < y := lt_of_not_ge h0
    have hL : (block410RightChunk001L : ℝ) = (block410RightChunk000R : ℝ) := by
      norm_num [block410RightChunk001L, block410RightChunk000R]
    have hR : (block410RightChunk001R : ℝ) = (block410RightR : ℝ) := by
      norm_num [block410RightChunk001R, block410RightR]
    have hyc : y ∈ Icc (block410RightChunk001L : ℝ) (block410RightChunk001R : ℝ) := by
      constructor
      · linarith [hprev, hL]
      · linarith [hy.2, hR]
    exact block410_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block410_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block410LeftL : ℝ) (block410LeftR : ℝ) →
    y ≠ 0 → y ≠ (block410S1 : ℝ) → y ≠ (block410S2 : ℝ) →
    y ≠ (block410S3 : ℝ) → y ≠ (block410S4 : ℝ) → 0 < block410V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block410RightL : ℝ) (block410RightR : ℝ) →
    y ≠ 0 → y ≠ (block410S1 : ℝ) → y ≠ (block410S2 : ℝ) →
    y ≠ (block410S3 : ℝ) → y ≠ (block410S4 : ℝ) → 0 < block410V y)

theorem block410_reallog_certificate_proof :
    block410_reallog_certificate := by
  exact ⟨block410_left_V_pos, block410_right_V_pos⟩

end Block410
end M1817475
end Erdos1038Lean
