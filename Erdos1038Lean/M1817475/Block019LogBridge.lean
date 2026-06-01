import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block019

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block019

open Set

def block019W1 : Rat := ((11159079135043253 : Rat) / 5000000000000000)
def block019W2 : Rat := (0 : Rat)
def block019W3 : Rat := (0 : Rat)
def block019W4 : Rat := ((7267969579983649 : Rat) / 25000000000000000)
def block019S1 : Rat := ((18174751 : Rat) / 10000000)
def block019S2 : Rat := ((511587 : Rat) / 200000)
def block019S3 : Rat := ((107000619 : Rat) / 40000000)
def block019S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block019V (y : ℝ) : ℝ :=
  ratPotential block019W1 block019W2 block019W3 block019W4 block019S1 block019S2 block019S3 block019S4 y

def block019LeftParamsCertificate : Bool :=
  allBoxesSameParams block019LeftBoxes block019W1 block019W2 block019W3 block019W4 block019S1 block019S2 block019S3 block019S4

theorem block019LeftParamsCertificate_eq_true :
    block019LeftParamsCertificate = true := by
  native_decide

theorem block019_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block019LeftL : ℝ) (block019LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block019S1 : ℝ))
    (hy2ne : y ≠ (block019S2 : ℝ))
    (hy3ne : y ≠ (block019S3 : ℝ))
    (hy4ne : y ≠ (block019S4 : ℝ)) :
    0 < block019V y := by
  have hcert := block019LeftCertificate_eq_true
  unfold block019LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block019LeftBoxes) (lo := block019LeftL) (hi := block019LeftR)
    (w1 := block019W1) (w2 := block019W2) (w3 := block019W3) (w4 := block019W4)
    (s1 := block019S1) (s2 := block019S2) (s3 := block019S3) (s4 := block019S4)
    hboxes hcover block019LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block019RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block019RightChunk000 block019W1 block019W2 block019W3 block019W4 block019S1 block019S2 block019S3 block019S4

theorem block019RightChunk000ParamsCertificate_eq_true :
    block019RightChunk000ParamsCertificate = true := by
  native_decide

theorem block019_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block019RightChunk000L : ℝ) (block019RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block019S1 : ℝ))
    (hy2ne : y ≠ (block019S2 : ℝ))
    (hy3ne : y ≠ (block019S3 : ℝ))
    (hy4ne : y ≠ (block019S4 : ℝ)) :
    0 < block019V y := by
  have hcert := block019RightChunk000Certificate_eq_true
  unfold block019RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block019RightChunk000) (lo := block019RightChunk000L) (hi := block019RightChunk000R)
    (w1 := block019W1) (w2 := block019W2) (w3 := block019W3) (w4 := block019W4)
    (s1 := block019S1) (s2 := block019S2) (s3 := block019S3) (s4 := block019S4)
    hboxes hcover block019RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block019RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block019RightChunk001 block019W1 block019W2 block019W3 block019W4 block019S1 block019S2 block019S3 block019S4

theorem block019RightChunk001ParamsCertificate_eq_true :
    block019RightChunk001ParamsCertificate = true := by
  native_decide

theorem block019_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block019RightChunk001L : ℝ) (block019RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block019S1 : ℝ))
    (hy2ne : y ≠ (block019S2 : ℝ))
    (hy3ne : y ≠ (block019S3 : ℝ))
    (hy4ne : y ≠ (block019S4 : ℝ)) :
    0 < block019V y := by
  have hcert := block019RightChunk001Certificate_eq_true
  unfold block019RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block019RightChunk001) (lo := block019RightChunk001L) (hi := block019RightChunk001R)
    (w1 := block019W1) (w2 := block019W2) (w3 := block019W3) (w4 := block019W4)
    (s1 := block019S1) (s2 := block019S2) (s3 := block019S3) (s4 := block019S4)
    hboxes hcover block019RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block019_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block019RightL : ℝ) (block019RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block019S1 : ℝ))
    (hy2ne : y ≠ (block019S2 : ℝ))
    (hy3ne : y ≠ (block019S3 : ℝ))
    (hy4ne : y ≠ (block019S4 : ℝ)) :
    0 < block019V y := by
  by_cases h0 : y ≤ (block019RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block019RightChunk000L : ℝ) (block019RightChunk000R : ℝ) := by
      have hL : (block019RightChunk000L : ℝ) = (block019RightL : ℝ) := by
        norm_num [block019RightChunk000L, block019RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block019_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    have hprev : (block019RightChunk000R : ℝ) < y := lt_of_not_ge h0
    have hL : (block019RightChunk001L : ℝ) = (block019RightChunk000R : ℝ) := by
      norm_num [block019RightChunk001L, block019RightChunk000R]
    have hR : (block019RightChunk001R : ℝ) = (block019RightR : ℝ) := by
      norm_num [block019RightChunk001R, block019RightR]
    have hyc : y ∈ Icc (block019RightChunk001L : ℝ) (block019RightChunk001R : ℝ) := by
      constructor
      · linarith [hprev, hL]
      · linarith [hy.2, hR]
    exact block019_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block019_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block019LeftL : ℝ) (block019LeftR : ℝ) →
    y ≠ 0 → y ≠ (block019S1 : ℝ) → y ≠ (block019S2 : ℝ) →
    y ≠ (block019S3 : ℝ) → y ≠ (block019S4 : ℝ) → 0 < block019V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block019RightL : ℝ) (block019RightR : ℝ) →
    y ≠ 0 → y ≠ (block019S1 : ℝ) → y ≠ (block019S2 : ℝ) →
    y ≠ (block019S3 : ℝ) → y ≠ (block019S4 : ℝ) → 0 < block019V y)

theorem block019_reallog_certificate_proof :
    block019_reallog_certificate := by
  exact ⟨block019_left_V_pos, block019_right_V_pos⟩

end Block019
end M1817475
end Erdos1038Lean
