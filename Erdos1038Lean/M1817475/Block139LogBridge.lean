import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block139

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block139

open Set

def block139W1 : Rat := ((25203558539109387 : Rat) / 10000000000000000)
def block139W2 : Rat := (0 : Rat)
def block139W3 : Rat := ((481746643627467 : Rat) / 4000000000000000)
def block139W4 : Rat := ((5955556401723089 : Rat) / 50000000000000000)
def block139S1 : Rat := ((18174751 : Rat) / 10000000)
def block139S2 : Rat := ((511587 : Rat) / 200000)
def block139S3 : Rat := ((136751561696428571297 : Rat) / 50000000000000000000)
def block139S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block139V (y : ℝ) : ℝ :=
  ratPotential block139W1 block139W2 block139W3 block139W4 block139S1 block139S2 block139S3 block139S4 y

def block139LeftParamsCertificate : Bool :=
  allBoxesSameParams block139LeftBoxes block139W1 block139W2 block139W3 block139W4 block139S1 block139S2 block139S3 block139S4

theorem block139LeftParamsCertificate_eq_true :
    block139LeftParamsCertificate = true := by
  native_decide

theorem block139_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block139LeftL : ℝ) (block139LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block139S1 : ℝ))
    (hy2ne : y ≠ (block139S2 : ℝ))
    (hy3ne : y ≠ (block139S3 : ℝ))
    (hy4ne : y ≠ (block139S4 : ℝ)) :
    0 < block139V y := by
  have hcert := block139LeftCertificate_eq_true
  unfold block139LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block139LeftBoxes) (lo := block139LeftL) (hi := block139LeftR)
    (w1 := block139W1) (w2 := block139W2) (w3 := block139W3) (w4 := block139W4)
    (s1 := block139S1) (s2 := block139S2) (s3 := block139S3) (s4 := block139S4)
    hboxes hcover block139LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block139RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block139RightChunk000 block139W1 block139W2 block139W3 block139W4 block139S1 block139S2 block139S3 block139S4

theorem block139RightChunk000ParamsCertificate_eq_true :
    block139RightChunk000ParamsCertificate = true := by
  native_decide

theorem block139_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block139RightChunk000L : ℝ) (block139RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block139S1 : ℝ))
    (hy2ne : y ≠ (block139S2 : ℝ))
    (hy3ne : y ≠ (block139S3 : ℝ))
    (hy4ne : y ≠ (block139S4 : ℝ)) :
    0 < block139V y := by
  have hcert := block139RightChunk000Certificate_eq_true
  unfold block139RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block139RightChunk000) (lo := block139RightChunk000L) (hi := block139RightChunk000R)
    (w1 := block139W1) (w2 := block139W2) (w3 := block139W3) (w4 := block139W4)
    (s1 := block139S1) (s2 := block139S2) (s3 := block139S3) (s4 := block139S4)
    hboxes hcover block139RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block139_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block139RightL : ℝ) (block139RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block139S1 : ℝ))
    (hy2ne : y ≠ (block139S2 : ℝ))
    (hy3ne : y ≠ (block139S3 : ℝ))
    (hy4ne : y ≠ (block139S4 : ℝ)) :
    0 < block139V y := by
  have hL : (block139RightChunk000L : ℝ) = (block139RightL : ℝ) := by
    norm_num [block139RightChunk000L, block139RightL]
  have hR : (block139RightChunk000R : ℝ) = (block139RightR : ℝ) := by
    norm_num [block139RightChunk000R, block139RightR]
  have hyc : y ∈ Icc (block139RightChunk000L : ℝ) (block139RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block139_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block139_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block139LeftL : ℝ) (block139LeftR : ℝ) →
    y ≠ 0 → y ≠ (block139S1 : ℝ) → y ≠ (block139S2 : ℝ) →
    y ≠ (block139S3 : ℝ) → y ≠ (block139S4 : ℝ) → 0 < block139V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block139RightL : ℝ) (block139RightR : ℝ) →
    y ≠ 0 → y ≠ (block139S1 : ℝ) → y ≠ (block139S2 : ℝ) →
    y ≠ (block139S3 : ℝ) → y ≠ (block139S4 : ℝ) → 0 < block139V y)

theorem block139_reallog_certificate_proof :
    block139_reallog_certificate := by
  exact ⟨block139_left_V_pos, block139_right_V_pos⟩

end Block139
end M1817475
end Erdos1038Lean
