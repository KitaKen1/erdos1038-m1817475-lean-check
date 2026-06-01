import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block289

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block289

open Set

def block289W1 : Rat := ((2571210071383349 : Rat) / 2500000000000000)
def block289W2 : Rat := ((9320436543321941 : Rat) / 250000000000000000)
def block289W3 : Rat := ((2804003434455281 : Rat) / 10000000000000000)
def block289W4 : Rat := (0 : Rat)
def block289S1 : Rat := ((18174751 : Rat) / 10000000)
def block289S2 : Rat := ((511587 : Rat) / 200000)
def block289S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block289S4 : Rat := ((69915275535714283201 : Rat) / 25000000000000000000)

noncomputable def block289V (y : ℝ) : ℝ :=
  ratPotential block289W1 block289W2 block289W3 block289W4 block289S1 block289S2 block289S3 block289S4 y

def block289LeftParamsCertificate : Bool :=
  allBoxesSameParams block289LeftBoxes block289W1 block289W2 block289W3 block289W4 block289S1 block289S2 block289S3 block289S4

theorem block289LeftParamsCertificate_eq_true :
    block289LeftParamsCertificate = true := by
  native_decide

theorem block289_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block289LeftL : ℝ) (block289LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block289S1 : ℝ))
    (hy2ne : y ≠ (block289S2 : ℝ))
    (hy3ne : y ≠ (block289S3 : ℝ))
    (hy4ne : y ≠ (block289S4 : ℝ)) :
    0 < block289V y := by
  have hcert := block289LeftCertificate_eq_true
  unfold block289LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block289LeftBoxes) (lo := block289LeftL) (hi := block289LeftR)
    (w1 := block289W1) (w2 := block289W2) (w3 := block289W3) (w4 := block289W4)
    (s1 := block289S1) (s2 := block289S2) (s3 := block289S3) (s4 := block289S4)
    hboxes hcover block289LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block289RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block289RightChunk000 block289W1 block289W2 block289W3 block289W4 block289S1 block289S2 block289S3 block289S4

theorem block289RightChunk000ParamsCertificate_eq_true :
    block289RightChunk000ParamsCertificate = true := by
  native_decide

theorem block289_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block289RightChunk000L : ℝ) (block289RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block289S1 : ℝ))
    (hy2ne : y ≠ (block289S2 : ℝ))
    (hy3ne : y ≠ (block289S3 : ℝ))
    (hy4ne : y ≠ (block289S4 : ℝ)) :
    0 < block289V y := by
  have hcert := block289RightChunk000Certificate_eq_true
  unfold block289RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block289RightChunk000) (lo := block289RightChunk000L) (hi := block289RightChunk000R)
    (w1 := block289W1) (w2 := block289W2) (w3 := block289W3) (w4 := block289W4)
    (s1 := block289S1) (s2 := block289S2) (s3 := block289S3) (s4 := block289S4)
    hboxes hcover block289RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block289_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block289RightL : ℝ) (block289RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block289S1 : ℝ))
    (hy2ne : y ≠ (block289S2 : ℝ))
    (hy3ne : y ≠ (block289S3 : ℝ))
    (hy4ne : y ≠ (block289S4 : ℝ)) :
    0 < block289V y := by
  have hL : (block289RightChunk000L : ℝ) = (block289RightL : ℝ) := by
    norm_num [block289RightChunk000L, block289RightL]
  have hR : (block289RightChunk000R : ℝ) = (block289RightR : ℝ) := by
    norm_num [block289RightChunk000R, block289RightR]
  have hyc : y ∈ Icc (block289RightChunk000L : ℝ) (block289RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block289_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block289_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block289LeftL : ℝ) (block289LeftR : ℝ) →
    y ≠ 0 → y ≠ (block289S1 : ℝ) → y ≠ (block289S2 : ℝ) →
    y ≠ (block289S3 : ℝ) → y ≠ (block289S4 : ℝ) → 0 < block289V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block289RightL : ℝ) (block289RightR : ℝ) →
    y ≠ 0 → y ≠ (block289S1 : ℝ) → y ≠ (block289S2 : ℝ) →
    y ≠ (block289S3 : ℝ) → y ≠ (block289S4 : ℝ) → 0 < block289V y)

theorem block289_reallog_certificate_proof :
    block289_reallog_certificate := by
  exact ⟨block289_left_V_pos, block289_right_V_pos⟩

end Block289
end M1817475
end Erdos1038Lean
