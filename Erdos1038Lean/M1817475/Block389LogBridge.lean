import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block389

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block389

open Set

def block389W1 : Rat := ((8082794833719401 : Rat) / 10000000000000000)
def block389W2 : Rat := ((10376311987954391 : Rat) / 250000000000000000)
def block389W3 : Rat := ((3408093925587421 : Rat) / 20000000000000000)
def block389W4 : Rat := ((7289432713918531 : Rat) / 50000000000000000)
def block389S1 : Rat := ((18174751 : Rat) / 10000000)
def block389S2 : Rat := ((511587 : Rat) / 200000)
def block389S3 : Rat := ((1060231636428571429 : Rat) / 400000000000000000)
def block389S4 : Rat := ((34776808526785713037 : Rat) / 12500000000000000000)

noncomputable def block389V (y : ℝ) : ℝ :=
  ratPotential block389W1 block389W2 block389W3 block389W4 block389S1 block389S2 block389S3 block389S4 y

def block389LeftParamsCertificate : Bool :=
  allBoxesSameParams block389LeftBoxes block389W1 block389W2 block389W3 block389W4 block389S1 block389S2 block389S3 block389S4

theorem block389LeftParamsCertificate_eq_true :
    block389LeftParamsCertificate = true := by
  native_decide

theorem block389_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block389LeftL : ℝ) (block389LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block389S1 : ℝ))
    (hy2ne : y ≠ (block389S2 : ℝ))
    (hy3ne : y ≠ (block389S3 : ℝ))
    (hy4ne : y ≠ (block389S4 : ℝ)) :
    0 < block389V y := by
  have hcert := block389LeftCertificate_eq_true
  unfold block389LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block389LeftBoxes) (lo := block389LeftL) (hi := block389LeftR)
    (w1 := block389W1) (w2 := block389W2) (w3 := block389W3) (w4 := block389W4)
    (s1 := block389S1) (s2 := block389S2) (s3 := block389S3) (s4 := block389S4)
    hboxes hcover block389LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block389RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block389RightChunk000 block389W1 block389W2 block389W3 block389W4 block389S1 block389S2 block389S3 block389S4

theorem block389RightChunk000ParamsCertificate_eq_true :
    block389RightChunk000ParamsCertificate = true := by
  native_decide

theorem block389_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block389RightChunk000L : ℝ) (block389RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block389S1 : ℝ))
    (hy2ne : y ≠ (block389S2 : ℝ))
    (hy3ne : y ≠ (block389S3 : ℝ))
    (hy4ne : y ≠ (block389S4 : ℝ)) :
    0 < block389V y := by
  have hcert := block389RightChunk000Certificate_eq_true
  unfold block389RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block389RightChunk000) (lo := block389RightChunk000L) (hi := block389RightChunk000R)
    (w1 := block389W1) (w2 := block389W2) (w3 := block389W3) (w4 := block389W4)
    (s1 := block389S1) (s2 := block389S2) (s3 := block389S3) (s4 := block389S4)
    hboxes hcover block389RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block389RightChunk001ParamsCertificate : Bool :=
  allBoxesSameParams block389RightChunk001 block389W1 block389W2 block389W3 block389W4 block389S1 block389S2 block389S3 block389S4

theorem block389RightChunk001ParamsCertificate_eq_true :
    block389RightChunk001ParamsCertificate = true := by
  native_decide

theorem block389_right_chunk001_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block389RightChunk001L : ℝ) (block389RightChunk001R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block389S1 : ℝ))
    (hy2ne : y ≠ (block389S2 : ℝ))
    (hy3ne : y ≠ (block389S3 : ℝ))
    (hy4ne : y ≠ (block389S4 : ℝ)) :
    0 < block389V y := by
  have hcert := block389RightChunk001Certificate_eq_true
  unfold block389RightChunk001Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block389RightChunk001) (lo := block389RightChunk001L) (hi := block389RightChunk001R)
    (w1 := block389W1) (w2 := block389W2) (w3 := block389W3) (w4 := block389W4)
    (s1 := block389S1) (s2 := block389S2) (s3 := block389S3) (s4 := block389S4)
    hboxes hcover block389RightChunk001ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block389_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block389RightL : ℝ) (block389RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block389S1 : ℝ))
    (hy2ne : y ≠ (block389S2 : ℝ))
    (hy3ne : y ≠ (block389S3 : ℝ))
    (hy4ne : y ≠ (block389S4 : ℝ)) :
    0 < block389V y := by
  by_cases h0 : y ≤ (block389RightChunk000R : ℝ)
  · have hyc : y ∈ Icc (block389RightChunk000L : ℝ) (block389RightChunk000R : ℝ) := by
      have hL : (block389RightChunk000L : ℝ) = (block389RightL : ℝ) := by
        norm_num [block389RightChunk000L, block389RightL]
      constructor
      · linarith [hy.1, hL]
      · exact h0
    exact block389_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne
  ·
    have hprev : (block389RightChunk000R : ℝ) < y := lt_of_not_ge h0
    have hL : (block389RightChunk001L : ℝ) = (block389RightChunk000R : ℝ) := by
      norm_num [block389RightChunk001L, block389RightChunk000R]
    have hR : (block389RightChunk001R : ℝ) = (block389RightR : ℝ) := by
      norm_num [block389RightChunk001R, block389RightR]
    have hyc : y ∈ Icc (block389RightChunk001L : ℝ) (block389RightChunk001R : ℝ) := by
      constructor
      · linarith [hprev, hL]
      · linarith [hy.2, hR]
    exact block389_right_chunk001_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block389_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block389LeftL : ℝ) (block389LeftR : ℝ) →
    y ≠ 0 → y ≠ (block389S1 : ℝ) → y ≠ (block389S2 : ℝ) →
    y ≠ (block389S3 : ℝ) → y ≠ (block389S4 : ℝ) → 0 < block389V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block389RightL : ℝ) (block389RightR : ℝ) →
    y ≠ 0 → y ≠ (block389S1 : ℝ) → y ≠ (block389S2 : ℝ) →
    y ≠ (block389S3 : ℝ) → y ≠ (block389S4 : ℝ) → 0 < block389V y)

theorem block389_reallog_certificate_proof :
    block389_reallog_certificate := by
  exact ⟨block389_left_V_pos, block389_right_V_pos⟩

end Block389
end M1817475
end Erdos1038Lean
