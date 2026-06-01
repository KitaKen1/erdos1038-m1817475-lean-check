import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block352

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block352

open Set

def block352W1 : Rat := ((9024572734552211 : Rat) / 10000000000000000)
def block352W2 : Rat := ((948893405498469 : Rat) / 20000000000000000)
def block352W3 : Rat := ((748122412504459 : Rat) / 5000000000000000)
def block352W4 : Rat := ((6917836042765413 : Rat) / 50000000000000000)
def block352S1 : Rat := ((18174751 : Rat) / 10000000)
def block352S2 : Rat := ((511587 : Rat) / 200000)
def block352S3 : Rat := ((133252271517857142879 : Rat) / 50000000000000000000)
def block352S4 : Rat := ((69309253214285711799 : Rat) / 25000000000000000000)

noncomputable def block352V (y : ℝ) : ℝ :=
  ratPotential block352W1 block352W2 block352W3 block352W4 block352S1 block352S2 block352S3 block352S4 y

def block352LeftParamsCertificate : Bool :=
  allBoxesSameParams block352LeftBoxes block352W1 block352W2 block352W3 block352W4 block352S1 block352S2 block352S3 block352S4

theorem block352LeftParamsCertificate_eq_true :
    block352LeftParamsCertificate = true := by
  native_decide

theorem block352_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block352LeftL : ℝ) (block352LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block352S1 : ℝ))
    (hy2ne : y ≠ (block352S2 : ℝ))
    (hy3ne : y ≠ (block352S3 : ℝ))
    (hy4ne : y ≠ (block352S4 : ℝ)) :
    0 < block352V y := by
  have hcert := block352LeftCertificate_eq_true
  unfold block352LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block352LeftBoxes) (lo := block352LeftL) (hi := block352LeftR)
    (w1 := block352W1) (w2 := block352W2) (w3 := block352W3) (w4 := block352W4)
    (s1 := block352S1) (s2 := block352S2) (s3 := block352S3) (s4 := block352S4)
    hboxes hcover block352LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block352RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block352RightChunk000 block352W1 block352W2 block352W3 block352W4 block352S1 block352S2 block352S3 block352S4

theorem block352RightChunk000ParamsCertificate_eq_true :
    block352RightChunk000ParamsCertificate = true := by
  native_decide

theorem block352_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block352RightChunk000L : ℝ) (block352RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block352S1 : ℝ))
    (hy2ne : y ≠ (block352S2 : ℝ))
    (hy3ne : y ≠ (block352S3 : ℝ))
    (hy4ne : y ≠ (block352S4 : ℝ)) :
    0 < block352V y := by
  have hcert := block352RightChunk000Certificate_eq_true
  unfold block352RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block352RightChunk000) (lo := block352RightChunk000L) (hi := block352RightChunk000R)
    (w1 := block352W1) (w2 := block352W2) (w3 := block352W3) (w4 := block352W4)
    (s1 := block352S1) (s2 := block352S2) (s3 := block352S3) (s4 := block352S4)
    hboxes hcover block352RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block352_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block352RightL : ℝ) (block352RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block352S1 : ℝ))
    (hy2ne : y ≠ (block352S2 : ℝ))
    (hy3ne : y ≠ (block352S3 : ℝ))
    (hy4ne : y ≠ (block352S4 : ℝ)) :
    0 < block352V y := by
  have hL : (block352RightChunk000L : ℝ) = (block352RightL : ℝ) := by
    norm_num [block352RightChunk000L, block352RightL]
  have hR : (block352RightChunk000R : ℝ) = (block352RightR : ℝ) := by
    norm_num [block352RightChunk000R, block352RightR]
  have hyc : y ∈ Icc (block352RightChunk000L : ℝ) (block352RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block352_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block352_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block352LeftL : ℝ) (block352LeftR : ℝ) →
    y ≠ 0 → y ≠ (block352S1 : ℝ) → y ≠ (block352S2 : ℝ) →
    y ≠ (block352S3 : ℝ) → y ≠ (block352S4 : ℝ) → 0 < block352V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block352RightL : ℝ) (block352RightR : ℝ) →
    y ≠ 0 → y ≠ (block352S1 : ℝ) → y ≠ (block352S2 : ℝ) →
    y ≠ (block352S3 : ℝ) → y ≠ (block352S4 : ℝ) → 0 < block352V y)

theorem block352_reallog_certificate_proof :
    block352_reallog_certificate := by
  exact ⟨block352_left_V_pos, block352_right_V_pos⟩

end Block352
end M1817475
end Erdos1038Lean
