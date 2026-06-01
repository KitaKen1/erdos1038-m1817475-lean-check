import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block314

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block314

open Set

def block314W1 : Rat := ((1198488392300747 : Rat) / 1250000000000000)
def block314W2 : Rat := ((3089862464016827 : Rat) / 50000000000000000)
def block314W3 : Rat := ((12911725786245337 : Rat) / 50000000000000000)
def block314W4 : Rat := (0 : Rat)
def block314S1 : Rat := ((18174751 : Rat) / 10000000)
def block314S2 : Rat := ((511587 : Rat) / 200000)
def block314S3 : Rat := ((27209558767857142837 : Rat) / 10000000000000000000)
def block314S4 : Rat := ((69973922857142854627 : Rat) / 25000000000000000000)

noncomputable def block314V (y : ℝ) : ℝ :=
  ratPotential block314W1 block314W2 block314W3 block314W4 block314S1 block314S2 block314S3 block314S4 y

def block314LeftParamsCertificate : Bool :=
  allBoxesSameParams block314LeftBoxes block314W1 block314W2 block314W3 block314W4 block314S1 block314S2 block314S3 block314S4

theorem block314LeftParamsCertificate_eq_true :
    block314LeftParamsCertificate = true := by
  native_decide

theorem block314_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block314LeftL : ℝ) (block314LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block314S1 : ℝ))
    (hy2ne : y ≠ (block314S2 : ℝ))
    (hy3ne : y ≠ (block314S3 : ℝ))
    (hy4ne : y ≠ (block314S4 : ℝ)) :
    0 < block314V y := by
  have hcert := block314LeftCertificate_eq_true
  unfold block314LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block314LeftBoxes) (lo := block314LeftL) (hi := block314LeftR)
    (w1 := block314W1) (w2 := block314W2) (w3 := block314W3) (w4 := block314W4)
    (s1 := block314S1) (s2 := block314S2) (s3 := block314S3) (s4 := block314S4)
    hboxes hcover block314LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block314RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block314RightChunk000 block314W1 block314W2 block314W3 block314W4 block314S1 block314S2 block314S3 block314S4

theorem block314RightChunk000ParamsCertificate_eq_true :
    block314RightChunk000ParamsCertificate = true := by
  native_decide

theorem block314_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block314RightChunk000L : ℝ) (block314RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block314S1 : ℝ))
    (hy2ne : y ≠ (block314S2 : ℝ))
    (hy3ne : y ≠ (block314S3 : ℝ))
    (hy4ne : y ≠ (block314S4 : ℝ)) :
    0 < block314V y := by
  have hcert := block314RightChunk000Certificate_eq_true
  unfold block314RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block314RightChunk000) (lo := block314RightChunk000L) (hi := block314RightChunk000R)
    (w1 := block314W1) (w2 := block314W2) (w3 := block314W3) (w4 := block314W4)
    (s1 := block314S1) (s2 := block314S2) (s3 := block314S3) (s4 := block314S4)
    hboxes hcover block314RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block314_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block314RightL : ℝ) (block314RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block314S1 : ℝ))
    (hy2ne : y ≠ (block314S2 : ℝ))
    (hy3ne : y ≠ (block314S3 : ℝ))
    (hy4ne : y ≠ (block314S4 : ℝ)) :
    0 < block314V y := by
  have hL : (block314RightChunk000L : ℝ) = (block314RightL : ℝ) := by
    norm_num [block314RightChunk000L, block314RightL]
  have hR : (block314RightChunk000R : ℝ) = (block314RightR : ℝ) := by
    norm_num [block314RightChunk000R, block314RightR]
  have hyc : y ∈ Icc (block314RightChunk000L : ℝ) (block314RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block314_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block314_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block314LeftL : ℝ) (block314LeftR : ℝ) →
    y ≠ 0 → y ≠ (block314S1 : ℝ) → y ≠ (block314S2 : ℝ) →
    y ≠ (block314S3 : ℝ) → y ≠ (block314S4 : ℝ) → 0 < block314V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block314RightL : ℝ) (block314RightR : ℝ) →
    y ≠ 0 → y ≠ (block314S1 : ℝ) → y ≠ (block314S2 : ℝ) →
    y ≠ (block314S3 : ℝ) → y ≠ (block314S4 : ℝ) → 0 < block314V y)

theorem block314_reallog_certificate_proof :
    block314_reallog_certificate := by
  exact ⟨block314_left_V_pos, block314_right_V_pos⟩

end Block314
end M1817475
end Erdos1038Lean
