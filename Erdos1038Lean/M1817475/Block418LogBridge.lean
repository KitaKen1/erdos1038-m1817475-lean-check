import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block418

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block418

open Set

def block418W1 : Rat := ((6927839202699161 : Rat) / 10000000000000000)
def block418W2 : Rat := (0 : Rat)
def block418W3 : Rat := ((184218444705853 : Rat) / 625000000000000)
def block418W4 : Rat := ((4292061630581529 : Rat) / 50000000000000000)
def block418S1 : Rat := ((18174751 : Rat) / 10000000)
def block418S2 : Rat := ((511587 : Rat) / 200000)
def block418S3 : Rat := ((131962030446428571507 : Rat) / 50000000000000000000)
def block418S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block418V (y : ℝ) : ℝ :=
  ratPotential block418W1 block418W2 block418W3 block418W4 block418S1 block418S2 block418S3 block418S4 y

def block418LeftParamsCertificate : Bool :=
  allBoxesSameParams block418LeftBoxes block418W1 block418W2 block418W3 block418W4 block418S1 block418S2 block418S3 block418S4

theorem block418LeftParamsCertificate_eq_true :
    block418LeftParamsCertificate = true := by
  native_decide

theorem block418_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block418LeftL : ℝ) (block418LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block418S1 : ℝ))
    (hy2ne : y ≠ (block418S2 : ℝ))
    (hy3ne : y ≠ (block418S3 : ℝ))
    (hy4ne : y ≠ (block418S4 : ℝ)) :
    0 < block418V y := by
  have hcert := block418LeftCertificate_eq_true
  unfold block418LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block418LeftBoxes) (lo := block418LeftL) (hi := block418LeftR)
    (w1 := block418W1) (w2 := block418W2) (w3 := block418W3) (w4 := block418W4)
    (s1 := block418S1) (s2 := block418S2) (s3 := block418S3) (s4 := block418S4)
    hboxes hcover block418LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block418RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block418RightChunk000 block418W1 block418W2 block418W3 block418W4 block418S1 block418S2 block418S3 block418S4

theorem block418RightChunk000ParamsCertificate_eq_true :
    block418RightChunk000ParamsCertificate = true := by
  native_decide

theorem block418_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block418RightChunk000L : ℝ) (block418RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block418S1 : ℝ))
    (hy2ne : y ≠ (block418S2 : ℝ))
    (hy3ne : y ≠ (block418S3 : ℝ))
    (hy4ne : y ≠ (block418S4 : ℝ)) :
    0 < block418V y := by
  have hcert := block418RightChunk000Certificate_eq_true
  unfold block418RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block418RightChunk000) (lo := block418RightChunk000L) (hi := block418RightChunk000R)
    (w1 := block418W1) (w2 := block418W2) (w3 := block418W3) (w4 := block418W4)
    (s1 := block418S1) (s2 := block418S2) (s3 := block418S3) (s4 := block418S4)
    hboxes hcover block418RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block418RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block418RightChunk001 block418W1 block418W2 block418W3 block418W4 block418S1 block418S2 block418S3 block418S4

theorem block418RightChunk001ParamsCertificate_eq_true :
    block418RightChunk001ParamsCertificate = true := by
  native_decide

theorem block418_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block418RightChunk001L : ℝ) (block418RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block418S1 : ℝ))
    (hy2ne : y ≠ (block418S2 : ℝ))
    (hy3ne : y ≠ (block418S3 : ℝ))
    (hy4ne : y ≠ (block418S4 : ℝ)) :
    0 < block418V y := by
  have hcert := block418RightChunk001Certificate_eq_true
  unfold block418RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block418RightChunk001) (lo := block418RightChunk001L) (hi := block418RightChunk001R)
    (w1 := block418W1) (w2 := block418W2) (w3 := block418W3) (w4 := block418W4)
    (s1 := block418S1) (s2 := block418S2) (s3 := block418S3) (s4 := block418S4)
    hboxes hcover block418RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block418_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block418RightL : ℝ) (block418RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block418S1 : ℝ))
    (hy2ne : y ≠ (block418S2 : ℝ))
    (hy3ne : y ≠ (block418S3 : ℝ))
    (hy4ne : y ≠ (block418S4 : ℝ)) :
    0 < block418V y := by
  by_cases h0 : y ≤ (block418RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block418RightChunk000L : ℝ) (block418RightChunk000R : ℝ) := by
      have hL : (block418RightChunk000L : ℝ) = (block418RightL : ℝ) := by
        norm_num [block418RightChunk000L, block418RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block418_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    have hprev : (block418RightChunk000R : ℝ) < y := lt_of_not_ge h0
    have hL : (block418RightChunk001L : ℝ) = (block418RightChunk000R : ℝ) := by
      norm_num [block418RightChunk001L, block418RightChunk000R]
    have hR : (block418RightChunk001R : ℝ) = (block418RightR : ℝ) := by
      norm_num [block418RightChunk001R, block418RightR]
    have hyc : y ∈ Icc (block418RightChunk001L : ℝ) (block418RightChunk001R : ℝ) := by
      constructor
      · linarith [hprev, hL]
      · linarith [hy.2, hR]
    exact block418_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block418_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block418LeftL : ℝ) (block418LeftR : ℝ) →
    y ≠ 0 → y ≠ (block418S1 : ℝ) → y ≠ (block418S2 : ℝ) →
    y ≠ (block418S3 : ℝ) → y ≠ (block418S4 : ℝ) → 0 < block418V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block418RightL : ℝ) (block418RightR : ℝ) →
    y ≠ 0 → y ≠ (block418S1 : ℝ) → y ≠ (block418S2 : ℝ) →
    y ≠ (block418S3 : ℝ) → y ≠ (block418S4 : ℝ) → 0 < block418V y)

theorem block418_reallog_certificate_proof :
    block418_reallog_certificate := by
  exact ⟨block418_left_V_pos, block418_right_V_pos⟩

end Block418
end M1817475
end Erdos1038Lean
