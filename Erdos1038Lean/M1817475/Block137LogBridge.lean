import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block137

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block137

open Set

def block137W1 : Rat := ((505653784831657 : Rat) / 200000000000000)
def block137W2 : Rat := (0 : Rat)
def block137W3 : Rat := ((11706057490045207 : Rat) / 100000000000000000)
def block137W4 : Rat := ((12289447779534149 : Rat) / 100000000000000000)
def block137S1 : Rat := ((18174751 : Rat) / 10000000)
def block137S2 : Rat := ((511587 : Rat) / 200000)
def block137S3 : Rat := ((136751561696428571297 : Rat) / 50000000000000000000)
def block137S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block137V (y : ℝ) : ℝ :=
  ratPotential block137W1 block137W2 block137W3 block137W4 block137S1 block137S2 block137S3 block137S4 y

def block137LeftParamsCertificate : Bool :=
  allBoxesSameParams block137LeftBoxes block137W1 block137W2 block137W3 block137W4 block137S1 block137S2 block137S3 block137S4

theorem block137LeftParamsCertificate_eq_true :
    block137LeftParamsCertificate = true := by
  native_decide

theorem block137_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block137LeftL : ℝ) (block137LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block137S1 : ℝ))
    (hy2ne : y ≠ (block137S2 : ℝ))
    (hy3ne : y ≠ (block137S3 : ℝ))
    (hy4ne : y ≠ (block137S4 : ℝ)) :
    0 < block137V y := by
  have hcert := block137LeftCertificate_eq_true
  unfold block137LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block137LeftBoxes) (lo := block137LeftL) (hi := block137LeftR)
    (w1 := block137W1) (w2 := block137W2) (w3 := block137W3) (w4 := block137W4)
    (s1 := block137S1) (s2 := block137S2) (s3 := block137S3) (s4 := block137S4)
    hboxes hcover block137LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block137RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block137RightChunk000 block137W1 block137W2 block137W3 block137W4 block137S1 block137S2 block137S3 block137S4

theorem block137RightChunk000ParamsCertificate_eq_true :
    block137RightChunk000ParamsCertificate = true := by
  native_decide

theorem block137_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block137RightChunk000L : ℝ) (block137RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block137S1 : ℝ))
    (hy2ne : y ≠ (block137S2 : ℝ))
    (hy3ne : y ≠ (block137S3 : ℝ))
    (hy4ne : y ≠ (block137S4 : ℝ)) :
    0 < block137V y := by
  have hcert := block137RightChunk000Certificate_eq_true
  unfold block137RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block137RightChunk000) (lo := block137RightChunk000L) (hi := block137RightChunk000R)
    (w1 := block137W1) (w2 := block137W2) (w3 := block137W3) (w4 := block137W4)
    (s1 := block137S1) (s2 := block137S2) (s3 := block137S3) (s4 := block137S4)
    hboxes hcover block137RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block137_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block137RightL : ℝ) (block137RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block137S1 : ℝ))
    (hy2ne : y ≠ (block137S2 : ℝ))
    (hy3ne : y ≠ (block137S3 : ℝ))
    (hy4ne : y ≠ (block137S4 : ℝ)) :
    0 < block137V y := by
  have hL : (block137RightChunk000L : ℝ) = (block137RightL : ℝ) := by
    norm_num [block137RightChunk000L, block137RightL]
  have hR : (block137RightChunk000R : ℝ) = (block137RightR : ℝ) := by
    norm_num [block137RightChunk000R, block137RightR]
  have hyc : y ∈ Icc (block137RightChunk000L : ℝ) (block137RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block137_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block137_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block137LeftL : ℝ) (block137LeftR : ℝ) →
    y ≠ 0 → y ≠ (block137S1 : ℝ) → y ≠ (block137S2 : ℝ) →
    y ≠ (block137S3 : ℝ) → y ≠ (block137S4 : ℝ) → 0 < block137V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block137RightL : ℝ) (block137RightR : ℝ) →
    y ≠ 0 → y ≠ (block137S1 : ℝ) → y ≠ (block137S2 : ℝ) →
    y ≠ (block137S3 : ℝ) → y ≠ (block137S4 : ℝ) → 0 < block137V y)

theorem block137_reallog_certificate_proof :
    block137_reallog_certificate := by
  exact ⟨block137_left_V_pos, block137_right_V_pos⟩

end Block137
end M1817475
end Erdos1038Lean
