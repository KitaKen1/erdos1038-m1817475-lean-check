import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block008

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block008

open Set

def block008W1 : Rat := ((2581271207474277 : Rat) / 250000000000000)
def block008W2 : Rat := (0 : Rat)
def block008W3 : Rat := (0 : Rat)
def block008W4 : Rat := ((2513038991523641 : Rat) / 10000000000000000)
def block008S1 : Rat := ((18174751 : Rat) / 10000000)
def block008S2 : Rat := ((511587 : Rat) / 200000)
def block008S3 : Rat := ((107000619 : Rat) / 40000000)
def block008S4 : Rat := ((3539260540178571301 : Rat) / 1250000000000000000)

noncomputable def block008V (y : ℝ) : ℝ :=
  ratPotential block008W1 block008W2 block008W3 block008W4 block008S1 block008S2 block008S3 block008S4 y

def block008LeftParamsCertificate : Bool :=
  allBoxesSameParams block008LeftBoxes block008W1 block008W2 block008W3 block008W4 block008S1 block008S2 block008S3 block008S4

theorem block008LeftParamsCertificate_eq_true :
    block008LeftParamsCertificate = true := by
  native_decide

theorem block008_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block008LeftL : ℝ) (block008LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block008S1 : ℝ))
    (hy2ne : y ≠ (block008S2 : ℝ))
    (hy3ne : y ≠ (block008S3 : ℝ))
    (hy4ne : y ≠ (block008S4 : ℝ)) :
    0 < block008V y := by
  have hcert := block008LeftCertificate_eq_true
  unfold block008LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block008LeftBoxes) (lo := block008LeftL) (hi := block008LeftR)
    (w1 := block008W1) (w2 := block008W2) (w3 := block008W3) (w4 := block008W4)
    (s1 := block008S1) (s2 := block008S2) (s3 := block008S3) (s4 := block008S4)
    hboxes hcover block008LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block008RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block008RightChunk000 block008W1 block008W2 block008W3 block008W4 block008S1 block008S2 block008S3 block008S4

theorem block008RightChunk000ParamsCertificate_eq_true :
    block008RightChunk000ParamsCertificate = true := by
  native_decide

theorem block008_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block008RightChunk000L : ℝ) (block008RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block008S1 : ℝ))
    (hy2ne : y ≠ (block008S2 : ℝ))
    (hy3ne : y ≠ (block008S3 : ℝ))
    (hy4ne : y ≠ (block008S4 : ℝ)) :
    0 < block008V y := by
  have hcert := block008RightChunk000Certificate_eq_true
  unfold block008RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block008RightChunk000) (lo := block008RightChunk000L) (hi := block008RightChunk000R)
    (w1 := block008W1) (w2 := block008W2) (w3 := block008W3) (w4 := block008W4)
    (s1 := block008S1) (s2 := block008S2) (s3 := block008S3) (s4 := block008S4)
    hboxes hcover block008RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block008_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block008RightL : ℝ) (block008RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block008S1 : ℝ))
    (hy2ne : y ≠ (block008S2 : ℝ))
    (hy3ne : y ≠ (block008S3 : ℝ))
    (hy4ne : y ≠ (block008S4 : ℝ)) :
    0 < block008V y := by
  have hL : (block008RightChunk000L : ℝ) = (block008RightL : ℝ) := by
    norm_num [block008RightChunk000L, block008RightL]
  have hR : (block008RightChunk000R : ℝ) = (block008RightR : ℝ) := by
    norm_num [block008RightChunk000R, block008RightR]
  have hyc : y ∈ Icc (block008RightChunk000L : ℝ) (block008RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block008_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block008_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block008LeftL : ℝ) (block008LeftR : ℝ) →
    y ≠ 0 → y ≠ (block008S1 : ℝ) → y ≠ (block008S2 : ℝ) →
    y ≠ (block008S3 : ℝ) → y ≠ (block008S4 : ℝ) → 0 < block008V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block008RightL : ℝ) (block008RightR : ℝ) →
    y ≠ 0 → y ≠ (block008S1 : ℝ) → y ≠ (block008S2 : ℝ) →
    y ≠ (block008S3 : ℝ) → y ≠ (block008S4 : ℝ) → 0 < block008V y)

theorem block008_reallog_certificate_proof :
    block008_reallog_certificate := by
  exact ⟨block008_left_V_pos, block008_right_V_pos⟩

end Block008
end M1817475
end Erdos1038Lean
