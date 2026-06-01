import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block166

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block166

open Set

def block166W1 : Rat := ((18388082096163807 : Rat) / 10000000000000000)
def block166W2 : Rat := (0 : Rat)
def block166W3 : Rat := ((8259590908151161 : Rat) / 50000000000000000)
def block166W4 : Rat := ((10299839505381593 : Rat) / 100000000000000000)
def block166S1 : Rat := ((18174751 : Rat) / 10000000)
def block166S2 : Rat := ((511587 : Rat) / 200000)
def block166S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block166S4 : Rat := ((27844905749999999 : Rat) / 10000000000000000)

noncomputable def block166V (y : ℝ) : ℝ :=
  ratPotential block166W1 block166W2 block166W3 block166W4 block166S1 block166S2 block166S3 block166S4 y

def block166LeftParamsCertificate : Bool :=
  allBoxesSameParams block166LeftBoxes block166W1 block166W2 block166W3 block166W4 block166S1 block166S2 block166S3 block166S4

theorem block166LeftParamsCertificate_eq_true :
    block166LeftParamsCertificate = true := by
  native_decide

theorem block166_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block166LeftL : ℝ) (block166LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block166S1 : ℝ))
    (hy2ne : y ≠ (block166S2 : ℝ))
    (hy3ne : y ≠ (block166S3 : ℝ))
    (hy4ne : y ≠ (block166S4 : ℝ)) :
    0 < block166V y := by
  have hcert := block166LeftCertificate_eq_true
  unfold block166LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block166LeftBoxes) (lo := block166LeftL) (hi := block166LeftR)
    (w1 := block166W1) (w2 := block166W2) (w3 := block166W3) (w4 := block166W4)
    (s1 := block166S1) (s2 := block166S2) (s3 := block166S3) (s4 := block166S4)
    hboxes hcover block166LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block166RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block166RightChunk000 block166W1 block166W2 block166W3 block166W4 block166S1 block166S2 block166S3 block166S4

theorem block166RightChunk000ParamsCertificate_eq_true :
    block166RightChunk000ParamsCertificate = true := by
  native_decide

theorem block166_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block166RightChunk000L : ℝ) (block166RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block166S1 : ℝ))
    (hy2ne : y ≠ (block166S2 : ℝ))
    (hy3ne : y ≠ (block166S3 : ℝ))
    (hy4ne : y ≠ (block166S4 : ℝ)) :
    0 < block166V y := by
  have hcert := block166RightChunk000Certificate_eq_true
  unfold block166RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block166RightChunk000) (lo := block166RightChunk000L) (hi := block166RightChunk000R)
    (w1 := block166W1) (w2 := block166W2) (w3 := block166W3) (w4 := block166W4)
    (s1 := block166S1) (s2 := block166S2) (s3 := block166S3) (s4 := block166S4)
    hboxes hcover block166RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block166_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block166RightL : ℝ) (block166RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block166S1 : ℝ))
    (hy2ne : y ≠ (block166S2 : ℝ))
    (hy3ne : y ≠ (block166S3 : ℝ))
    (hy4ne : y ≠ (block166S4 : ℝ)) :
    0 < block166V y := by
  have hL : (block166RightChunk000L : ℝ) = (block166RightL : ℝ) := by
    norm_num [block166RightChunk000L, block166RightL]
  have hR : (block166RightChunk000R : ℝ) = (block166RightR : ℝ) := by
    norm_num [block166RightChunk000R, block166RightR]
  have hyc : y ∈ Icc (block166RightChunk000L : ℝ) (block166RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block166_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block166_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block166LeftL : ℝ) (block166LeftR : ℝ) →
    y ≠ 0 → y ≠ (block166S1 : ℝ) → y ≠ (block166S2 : ℝ) →
    y ≠ (block166S3 : ℝ) → y ≠ (block166S4 : ℝ) → 0 < block166V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block166RightL : ℝ) (block166RightR : ℝ) →
    y ≠ 0 → y ≠ (block166S1 : ℝ) → y ≠ (block166S2 : ℝ) →
    y ≠ (block166S3 : ℝ) → y ≠ (block166S4 : ℝ) → 0 < block166V y)

theorem block166_reallog_certificate_proof :
    block166_reallog_certificate := by
  exact ⟨block166_left_V_pos, block166_right_V_pos⟩

end Block166
end M1817475
end Erdos1038Lean
