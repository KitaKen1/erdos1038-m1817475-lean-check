import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block267

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block267

open Set

def block267W1 : Rat := ((10288982383505731 : Rat) / 10000000000000000)
def block267W2 : Rat := ((556237522700637 : Rat) / 20000000000000000)
def block267W3 : Rat := ((2949989043960091 : Rat) / 10000000000000000)
def block267W4 : Rat := (0 : Rat)
def block267S1 : Rat := ((18174751 : Rat) / 10000000)
def block267S2 : Rat := ((511587 : Rat) / 200000)
def block267S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block267S4 : Rat := ((69915275535714283201 : Rat) / 25000000000000000000)

noncomputable def block267V (y : ℝ) : ℝ :=
  ratPotential block267W1 block267W2 block267W3 block267W4 block267S1 block267S2 block267S3 block267S4 y

def block267LeftParamsCertificate : Bool :=
  allBoxesSameParams block267LeftBoxes block267W1 block267W2 block267W3 block267W4 block267S1 block267S2 block267S3 block267S4

theorem block267LeftParamsCertificate_eq_true :
    block267LeftParamsCertificate = true := by
  native_decide

theorem block267_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block267LeftL : ℝ) (block267LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block267S1 : ℝ))
    (hy2ne : y ≠ (block267S2 : ℝ))
    (hy3ne : y ≠ (block267S3 : ℝ))
    (hy4ne : y ≠ (block267S4 : ℝ)) :
    0 < block267V y := by
  have hcert := block267LeftCertificate_eq_true
  unfold block267LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block267LeftBoxes) (lo := block267LeftL) (hi := block267LeftR)
    (w1 := block267W1) (w2 := block267W2) (w3 := block267W3) (w4 := block267W4)
    (s1 := block267S1) (s2 := block267S2) (s3 := block267S3) (s4 := block267S4)
    hboxes hcover block267LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block267RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block267RightChunk000 block267W1 block267W2 block267W3 block267W4 block267S1 block267S2 block267S3 block267S4

theorem block267RightChunk000ParamsCertificate_eq_true :
    block267RightChunk000ParamsCertificate = true := by
  native_decide

theorem block267_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block267RightChunk000L : ℝ) (block267RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block267S1 : ℝ))
    (hy2ne : y ≠ (block267S2 : ℝ))
    (hy3ne : y ≠ (block267S3 : ℝ))
    (hy4ne : y ≠ (block267S4 : ℝ)) :
    0 < block267V y := by
  have hcert := block267RightChunk000Certificate_eq_true
  unfold block267RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block267RightChunk000) (lo := block267RightChunk000L) (hi := block267RightChunk000R)
    (w1 := block267W1) (w2 := block267W2) (w3 := block267W3) (w4 := block267W4)
    (s1 := block267S1) (s2 := block267S2) (s3 := block267S3) (s4 := block267S4)
    hboxes hcover block267RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block267RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block267RightChunk001 block267W1 block267W2 block267W3 block267W4 block267S1 block267S2 block267S3 block267S4

theorem block267RightChunk001ParamsCertificate_eq_true :
    block267RightChunk001ParamsCertificate = true := by
  native_decide

theorem block267_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block267RightChunk001L : ℝ) (block267RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block267S1 : ℝ))
    (hy2ne : y ≠ (block267S2 : ℝ))
    (hy3ne : y ≠ (block267S3 : ℝ))
    (hy4ne : y ≠ (block267S4 : ℝ)) :
    0 < block267V y := by
  have hcert := block267RightChunk001Certificate_eq_true
  unfold block267RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block267RightChunk001) (lo := block267RightChunk001L) (hi := block267RightChunk001R)
    (w1 := block267W1) (w2 := block267W2) (w3 := block267W3) (w4 := block267W4)
    (s1 := block267S1) (s2 := block267S2) (s3 := block267S3) (s4 := block267S4)
    hboxes hcover block267RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block267_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block267RightL : ℝ) (block267RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block267S1 : ℝ))
    (hy2ne : y ≠ (block267S2 : ℝ))
    (hy3ne : y ≠ (block267S3 : ℝ))
    (hy4ne : y ≠ (block267S4 : ℝ)) :
    0 < block267V y := by
  by_cases h0 : y ≤ (block267RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block267RightChunk000L : ℝ) (block267RightChunk000R : ℝ) := by
      have hL : (block267RightChunk000L : ℝ) = (block267RightL : ℝ) := by
        norm_num [block267RightChunk000L, block267RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block267_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    have hprev : (block267RightChunk000R : ℝ) < y := lt_of_not_ge h0
    have hL : (block267RightChunk001L : ℝ) = (block267RightChunk000R : ℝ) := by
      norm_num [block267RightChunk001L, block267RightChunk000R]
    have hR : (block267RightChunk001R : ℝ) = (block267RightR : ℝ) := by
      norm_num [block267RightChunk001R, block267RightR]
    have hyc : y ∈ Icc (block267RightChunk001L : ℝ) (block267RightChunk001R : ℝ) := by
      constructor
      · linarith [hprev, hL]
      · linarith [hy.2, hR]
    exact block267_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block267_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block267LeftL : ℝ) (block267LeftR : ℝ) →
    y ≠ 0 → y ≠ (block267S1 : ℝ) → y ≠ (block267S2 : ℝ) →
    y ≠ (block267S3 : ℝ) → y ≠ (block267S4 : ℝ) → 0 < block267V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block267RightL : ℝ) (block267RightR : ℝ) →
    y ≠ 0 → y ≠ (block267S1 : ℝ) → y ≠ (block267S2 : ℝ) →
    y ≠ (block267S3 : ℝ) → y ≠ (block267S4 : ℝ) → 0 < block267V y)

theorem block267_reallog_certificate_proof :
    block267_reallog_certificate := by
  exact ⟨block267_left_V_pos, block267_right_V_pos⟩

end Block267
end M1817475
end Erdos1038Lean
