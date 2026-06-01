import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block478

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block478

open Set

def block478W1 : Rat := ((162465760909253 : Rat) / 312500000000000)
def block478W2 : Rat := (0 : Rat)
def block478W3 : Rat := ((3748155273022217 : Rat) / 10000000000000000)
def block478W4 : Rat := ((5501511648240697 : Rat) / 125000000000000000)
def block478S1 : Rat := ((18174751 : Rat) / 10000000)
def block478S2 : Rat := ((511587 : Rat) / 200000)
def block478S3 : Rat := ((130789084017857142987 : Rat) / 50000000000000000000)
def block478S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block478V (y : ℝ) : ℝ :=
  ratPotential block478W1 block478W2 block478W3 block478W4 block478S1 block478S2 block478S3 block478S4 y

def block478LeftParamsCertificate : Bool :=
  allBoxesSameParams block478LeftBoxes block478W1 block478W2 block478W3 block478W4 block478S1 block478S2 block478S3 block478S4

theorem block478LeftParamsCertificate_eq_true :
    block478LeftParamsCertificate = true := by
  native_decide

theorem block478_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block478LeftL : ℝ) (block478LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block478S1 : ℝ))
    (hy2ne : y ≠ (block478S2 : ℝ))
    (hy3ne : y ≠ (block478S3 : ℝ))
    (hy4ne : y ≠ (block478S4 : ℝ)) :
    0 < block478V y := by
  have hcert := block478LeftCertificate_eq_true
  unfold block478LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block478LeftBoxes) (lo := block478LeftL) (hi := block478LeftR)
    (w1 := block478W1) (w2 := block478W2) (w3 := block478W3) (w4 := block478W4)
    (s1 := block478S1) (s2 := block478S2) (s3 := block478S3) (s4 := block478S4)
    hboxes hcover block478LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block478RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block478RightChunk000 block478W1 block478W2 block478W3 block478W4 block478S1 block478S2 block478S3 block478S4

theorem block478RightChunk000ParamsCertificate_eq_true :
    block478RightChunk000ParamsCertificate = true := by
  native_decide

theorem block478_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block478RightChunk000L : ℝ) (block478RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block478S1 : ℝ))
    (hy2ne : y ≠ (block478S2 : ℝ))
    (hy3ne : y ≠ (block478S3 : ℝ))
    (hy4ne : y ≠ (block478S4 : ℝ)) :
    0 < block478V y := by
  have hcert := block478RightChunk000Certificate_eq_true
  unfold block478RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block478RightChunk000) (lo := block478RightChunk000L) (hi := block478RightChunk000R)
    (w1 := block478W1) (w2 := block478W2) (w3 := block478W3) (w4 := block478W4)
    (s1 := block478S1) (s2 := block478S2) (s3 := block478S3) (s4 := block478S4)
    hboxes hcover block478RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block478_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block478RightL : ℝ) (block478RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block478S1 : ℝ))
    (hy2ne : y ≠ (block478S2 : ℝ))
    (hy3ne : y ≠ (block478S3 : ℝ))
    (hy4ne : y ≠ (block478S4 : ℝ)) :
    0 < block478V y := by
  have hL : (block478RightChunk000L : ℝ) = (block478RightL : ℝ) := by
    norm_num [block478RightChunk000L, block478RightL]
  have hR : (block478RightChunk000R : ℝ) = (block478RightR : ℝ) := by
    norm_num [block478RightChunk000R, block478RightR]
  have hyc : y ∈ Icc (block478RightChunk000L : ℝ) (block478RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block478_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block478_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block478LeftL : ℝ) (block478LeftR : ℝ) →
    y ≠ 0 → y ≠ (block478S1 : ℝ) → y ≠ (block478S2 : ℝ) →
    y ≠ (block478S3 : ℝ) → y ≠ (block478S4 : ℝ) → 0 < block478V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block478RightL : ℝ) (block478RightR : ℝ) →
    y ≠ 0 → y ≠ (block478S1 : ℝ) → y ≠ (block478S2 : ℝ) →
    y ≠ (block478S3 : ℝ) → y ≠ (block478S4 : ℝ) → 0 < block478V y)

theorem block478_reallog_certificate_proof :
    block478_reallog_certificate := by
  exact ⟨block478_left_V_pos, block478_right_V_pos⟩

end Block478
end M1817475
end Erdos1038Lean
