import Erdos1038Lean.LogBridge
import Erdos1038Lean.M1817475.Block364

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Erdos1038Lean
namespace M1817475
namespace Block364

open Set

def block364W1 : Rat := ((439452233163061 : Rat) / 500000000000000)
def block364W2 : Rat := ((2363670877726161 : Rat) / 50000000000000000)
def block364W3 : Rat := ((3061891501628649 : Rat) / 20000000000000000)
def block364W4 : Rat := ((696339742839641 : Rat) / 5000000000000000)
def block364S1 : Rat := ((18174751 : Rat) / 10000000)
def block364S2 : Rat := ((511587 : Rat) / 200000)
def block364S3 : Rat := ((5320707289285714287 : Rat) / 2000000000000000000)
def block364S4 : Rat := ((69309253214285711799 : Rat) / 25000000000000000000)

noncomputable def block364V (y : ℝ) : ℝ :=
  ratPotential block364W1 block364W2 block364W3 block364W4 block364S1 block364S2 block364S3 block364S4 y

def block364LeftParamsCertificate : Bool :=
  allBoxesSameParams block364LeftBoxes block364W1 block364W2 block364W3 block364W4 block364S1 block364S2 block364S3 block364S4

theorem block364LeftParamsCertificate_eq_true :
    block364LeftParamsCertificate = true := by
  native_decide

theorem block364_left_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block364LeftL : ℝ) (block364LeftR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block364S1 : ℝ))
    (hy2ne : y ≠ (block364S2 : ℝ))
    (hy3ne : y ≠ (block364S3 : ℝ))
    (hy4ne : y ≠ (block364S4 : ℝ)) :
    0 < block364V y := by
  have hcert := block364LeftCertificate_eq_true
  unfold block364LeftCertificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block364LeftBoxes) (lo := block364LeftL) (hi := block364LeftR)
    (w1 := block364W1) (w2 := block364W2) (w3 := block364W3) (w4 := block364W4)
    (s1 := block364S1) (s2 := block364S2) (s3 := block364S3) (s4 := block364S4)
    hboxes hcover block364LeftParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

def block364RightChunk000ParamsCertificate : Bool :=
  allBoxesSameParams block364RightChunk000 block364W1 block364W2 block364W3 block364W4 block364S1 block364S2 block364S3 block364S4

theorem block364RightChunk000ParamsCertificate_eq_true :
    block364RightChunk000ParamsCertificate = true := by
  native_decide

theorem block364_right_chunk000_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block364RightChunk000L : ℝ) (block364RightChunk000R : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block364S1 : ℝ))
    (hy2ne : y ≠ (block364S2 : ℝ))
    (hy3ne : y ≠ (block364S3 : ℝ))
    (hy4ne : y ≠ (block364S4 : ℝ)) :
    0 < block364V y := by
  have hcert := block364RightChunk000Certificate_eq_true
  unfold block364RightChunk000Certificate at hcert
  have hboxes := bool_left_of_and_eq_true hcert
  have hcover := bool_right_of_and_eq_true hcert
  exact ratPotential_pos_of_allBoxesValid_covers_sameParams
    (boxes := block364RightChunk000) (lo := block364RightChunk000L) (hi := block364RightChunk000R)
    (w1 := block364W1) (w2 := block364W2) (w3 := block364W3) (w4 := block364W4)
    (s1 := block364S1) (s2 := block364S2) (s3 := block364S3) (s4 := block364S4)
    hboxes hcover block364RightChunk000ParamsCertificate_eq_true hy hy0ne hy1ne hy2ne hy3ne hy4ne

theorem block364_right_V_pos
    {y : ℝ}
    (hy : y ∈ Icc (block364RightL : ℝ) (block364RightR : ℝ))
    (hy0ne : y ≠ 0)
    (hy1ne : y ≠ (block364S1 : ℝ))
    (hy2ne : y ≠ (block364S2 : ℝ))
    (hy3ne : y ≠ (block364S3 : ℝ))
    (hy4ne : y ≠ (block364S4 : ℝ)) :
    0 < block364V y := by
  have hL : (block364RightChunk000L : ℝ) = (block364RightL : ℝ) := by
    norm_num [block364RightChunk000L, block364RightL]
  have hR : (block364RightChunk000R : ℝ) = (block364RightR : ℝ) := by
    norm_num [block364RightChunk000R, block364RightR]
  have hyc : y ∈ Icc (block364RightChunk000L : ℝ) (block364RightChunk000R : ℝ) := by
    constructor <;> linarith [hy.1, hy.2, hL, hR]
  exact block364_right_chunk000_V_pos hyc hy0ne hy1ne hy2ne hy3ne hy4ne

def block364_reallog_certificate : Prop :=
  (∀ {y : ℝ}, y ∈ Icc (block364LeftL : ℝ) (block364LeftR : ℝ) →
    y ≠ 0 → y ≠ (block364S1 : ℝ) → y ≠ (block364S2 : ℝ) →
    y ≠ (block364S3 : ℝ) → y ≠ (block364S4 : ℝ) → 0 < block364V y) /\
  (∀ {y : ℝ}, y ∈ Icc (block364RightL : ℝ) (block364RightR : ℝ) →
    y ≠ 0 → y ≠ (block364S1 : ℝ) → y ≠ (block364S2 : ℝ) →
    y ≠ (block364S3 : ℝ) → y ≠ (block364S4 : ℝ) → 0 < block364V y)

theorem block364_reallog_certificate_proof :
    block364_reallog_certificate := by
  exact ⟨block364_left_V_pos, block364_right_V_pos⟩

end Block364
end M1817475
end Erdos1038Lean
