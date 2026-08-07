import Challenge.EvmProof.CertifiedArtifact

set_option warningAsError true

/-! Curated, bytecode-certified snapshots used by legacy RIPEMD proof APIs.

The source artifact is `Challenge/Ripemd160/Reference/reference.hex`.
`Artifact.snapshotRows_eq` kernel-checks these cached entries against the
structurally derived instruction table.
-/

namespace Challenge.Ripemd160.Reference.Proofs.Bytecode.ArtifactSnapshots

open EvmSemantics EvmSemantics.EVM YulEvmCompiler

abbrev op (opcode : UInt8) : Instr :=
  match Decode.opcodeOf opcode with
  | some decoded => .op decoded
  | none => .op .INVALID

@[simp] theorem op_jump : op 0x56 = .op .JUMP := by rfl
@[simp] theorem op_jumpdest : op 0x5b = .op .JUMPDEST := by rfl
@[simp] theorem op_mstore : op 0x52 = .op .MSTORE := by rfl
@[simp] theorem op_add : op 0x01 = .op .ADD := by rfl
@[simp] theorem op_sub : op 0x03 = .op .SUB := by rfl
@[simp] theorem op_shl : op 0x1b = .op .SHL := by rfl
@[simp] theorem op_shr : op 0x1c = .op .SHR := by rfl
@[simp] theorem op_calldatasize : op 0x36 = .op .CALLDATASIZE := by rfl
@[simp] theorem op_calldatacopy : op 0x37 = .op .CALLDATACOPY := by rfl
@[simp] theorem op_mstore8 : op 0x53 = .op .MSTORE8 := by rfl
@[simp] theorem op_pop : op 0x50 = .op .POP := by rfl
@[simp] theorem op_dup1 : op 0x80 = .op (.Dup ⟨0, by decide⟩) := by rfl
@[simp] theorem op_dup2 : op 0x81 = .op (.Dup ⟨1, by decide⟩) := by rfl
@[simp] theorem op_dup4 : op 0x83 = .op (.Dup ⟨3, by decide⟩) := by rfl
@[simp] theorem op_swap2 : op 0x91 = .op (.Swap ⟨1, by decide⟩) := by rfl

/-- Instruction indices referenced by retained compatibility proofs. -/
def indices : List (Fin 831) :=
[
  0, 1, 20, 21, 22, 35, 36, 37, 52, 53, 54, 67,
  68, 69, 83, 84, 85, 105, 106, 107, 205, 206, 207, 313,
  314, 315, 346, 347, 348, 349, 350, 351, 352, 353, 354, 355,
  356, 357, 358, 359, 360, 361, 362, 363, 364, 365, 366, 367,
  368, 369, 370, 371, 372, 373, 374, 375, 376, 377, 378, 379,
  380, 381, 382, 383, 384, 385, 386, 387, 388, 389, 390, 391,
  392, 393, 394, 395, 396, 397, 398, 399, 400, 401, 402, 403,
  404, 405, 406, 407, 408, 409, 410, 411, 412, 448, 449, 450,
  647, 648, 649, 682, 683, 684, 685, 686, 687, 688, 689, 690,
  691, 692, 693, 694, 695, 696, 697, 698, 699, 700, 701, 702,
  703, 704, 705, 706, 707, 708, 709, 710, 711, 712, 713, 714,
  715, 716, 717, 718, 719, 720, 721, 722, 723, 724, 725, 726,
  727, 728, 729, 730, 731, 732, 733, 734, 735, 736, 737, 738,
  739, 740, 741, 742, 743, 744, 745, 746, 747, 748, 749, 750,
  751, 752, 753, 754, 755, 756, 757, 758, 759, 760, 761, 762,
  763, 764, 765, 766, 767
]

/-- Cached entries at the listed indices; Artifact checks the whole list
against the structurally derived table with one definitional equality. -/
def entries : List Challenge.EvmProof.CertifiedArtifact.Entry :=
[
  ⟨0, .push 2 27⟩,
  ⟨3, op 0x56⟩,
  ⟨27, op 0x5b⟩,
  ⟨28, .push 2 46⟩,
  ⟨31, op 0x56⟩,
  ⟨46, op 0x5b⟩,
  ⟨47, .push 2 70⟩,
  ⟨50, op 0x56⟩,
  ⟨70, op 0x5b⟩,
  ⟨71, .push 2 90⟩,
  ⟨74, op 0x56⟩,
  ⟨90, op 0x5b⟩,
  ⟨91, .push 2 115⟩,
  ⟨94, op 0x56⟩,
  ⟨115, op 0x5b⟩,
  ⟨116, .push 2 142⟩,
  ⟨119, op 0x56⟩,
  ⟨142, op 0x5b⟩,
  ⟨143, .push 2 271⟩,
  ⟨146, op 0x56⟩,
  ⟨271, op 0x5b⟩,
  ⟨272, .push 2 434⟩,
  ⟨275, op 0x56⟩,
  ⟨434, op 0x5b⟩,
  ⟨435, .push 2 475⟩,
  ⟨438, op 0x56⟩,
  ⟨475, op 0x5b⟩,
  ⟨476, .push 2 561⟩,
  ⟨479, op 0x56⟩,
  ⟨480, op 0x5b⟩,
  ⟨481, op 0x36⟩,
  ⟨482, .push 1 72⟩,
  ⟨484, op 0x81⟩,
  ⟨485, op 0x01⟩,
  ⟨486, .push 1 6⟩,
  ⟨488, op 0x1c⟩,
  ⟨489, .push 1 6⟩,
  ⟨491, op 0x1b⟩,
  ⟨492, op 0x91⟩,
  ⟨493, op 0x50⟩,
  ⟨494, op 0x80⟩,
  ⟨495, .push 0 0⟩,
  ⟨496, .push 2 2048⟩,
  ⟨499, op 0x37⟩,
  ⟨500, .push 1 128⟩,
  ⟨502, op 0x81⟩,
  ⟨503, .push 2 2048⟩,
  ⟨506, op 0x01⟩,
  ⟨507, op 0x53⟩,
  ⟨508, op 0x80⟩,
  ⟨509, .push 1 3⟩,
  ⟨511, op 0x1b⟩,
  ⟨512, .push 1 8⟩,
  ⟨514, op 0x83⟩,
  ⟨515, op 0x03⟩,
  ⟨516, .push 2 2048⟩,
  ⟨519, op 0x01⟩,
  ⟨520, .push 0 0⟩,
  ⟨521, op 0x5b⟩,
  ⟨522, .push 1 8⟩,
  ⟨524, op 0x81⟩,
  ⟨525, op 0x10⟩,
  ⟨526, op 0x15⟩,
  ⟨527, .push 2 554⟩,
  ⟨530, op 0x57⟩,
  ⟨531, .push 1 255⟩,
  ⟨533, op 0x83⟩,
  ⟨534, op 0x82⟩,
  ⟨535, .push 1 3⟩,
  ⟨537, op 0x1b⟩,
  ⟨538, op 0x1c⟩,
  ⟨539, op 0x16⟩,
  ⟨540, op 0x81⟩,
  ⟨541, op 0x83⟩,
  ⟨542, op 0x01⟩,
  ⟨543, op 0x53⟩,
  ⟨544, .push 1 1⟩,
  ⟨546, op 0x81⟩,
  ⟨547, op 0x01⟩,
  ⟨548, op 0x90⟩,
  ⟨549, op 0x50⟩,
  ⟨550, .push 2 521⟩,
  ⟨553, op 0x56⟩,
  ⟨554, op 0x5b⟩,
  ⟨555, op 0x50⟩,
  ⟨556, op 0x50⟩,
  ⟨557, op 0x50⟩,
  ⟨558, op 0x50⟩,
  ⟨559, op 0x90⟩,
  ⟨560, op 0x56⟩,
  ⟨561, op 0x5b⟩,
  ⟨562, .push 2 616⟩,
  ⟨565, op 0x56⟩,
  ⟨616, op 0x5b⟩,
  ⟨617, .push 2 961⟩,
  ⟨620, op 0x56⟩,
  ⟨961, op 0x5b⟩,
  ⟨962, .push 2 1006⟩,
  ⟨965, op 0x56⟩,
  ⟨1006, op 0x5b⟩,
  ⟨1007, .push 31 1780731860627700044960722568376592188711674974810043212252563479055960840⟩,
  ⟨1039, .push 2 1184⟩,
  ⟨1042, op 0x52⟩,
  ⟨1043, .push 32 1374703749640218873849524064026661036561295975619335768036000015621818746370⟩,
  ⟨1076, .push 2 1216⟩,
  ⟨1079, op 0x52⟩,
  ⟨1080, .push 32 1809286146446445343010337679715913357291520642540487409382712519614204477440⟩,
  ⟨1113, .push 2 1248⟩,
  ⟨1116, op 0x52⟩,
  ⟨1117, .push 32 2286348414996307935469207465186628553155355030353023797310855598864584999170⟩,
  ⟨1150, .push 2 1280⟩,
  ⟨1153, op 0x52⟩,
  ⟨1154, .push 32 6793533947442029545286681365244130742947859423983440781638017424580845963790⟩,
  ⟨1187, .push 2 1312⟩,
  ⟨1190, op 0x52⟩,
  ⟨1191, .push 32 5454326014381509071620663843103927214778145566039445656282506490595801825280⟩,
  ⟨1224, .push 2 1344⟩,
  ⟨1227, op 0x52⟩,
  ⟨1228, .push 32 5000281043567253289773844389228683908720941172611121566642559091978571025676⟩,
  ⟨1261, .push 2 1376⟩,
  ⟨1264, op 0x52⟩,
  ⟨1265, .push 32 4998451946933852135137276647445154408072640462072745561656555001729660617996⟩,
  ⟨1298, .push 2 1408⟩,
  ⟨1301, op 0x52⟩,
  ⟨1302, .push 32 4097353149147406276549177442451244923784709130172834976461593227075946283008⟩,
  ⟨1335, .push 2 1440⟩,
  ⟨1338, op 0x52⟩,
  ⟨1339, .push 32 3634466825900925589093651101374881051901026410458987220032629834781140389131⟩,
  ⟨1372, .push 2 1472⟩,
  ⟨1375, op 0x52⟩,
  ⟨1376, .push 32 4083287390302437702768465126624575726298108573653391417181074648310269415176⟩,
  ⟨1409, .push 2 1504⟩,
  ⟨1412, op 0x52⟩,
  ⟨1413, .push 32 3627420088851531435467691758328083203359072412578514691593700216701345333248⟩,
  ⟨1446, .push 2 1536⟩,
  ⟨1449, op 0x52⟩,
  ⟨1450, .push 0 0⟩,
  ⟨1451, .push 2 1568⟩,
  ⟨1454, op 0x52⟩,
  ⟨1455, .push 4 1518500249⟩,
  ⟨1460, .push 2 1600⟩,
  ⟨1463, op 0x52⟩,
  ⟨1464, .push 4 1859775393⟩,
  ⟨1469, .push 2 1632⟩,
  ⟨1472, op 0x52⟩,
  ⟨1473, .push 4 2400959708⟩,
  ⟨1478, .push 2 1664⟩,
  ⟨1481, op 0x52⟩,
  ⟨1482, .push 4 2840853838⟩,
  ⟨1487, .push 2 1696⟩,
  ⟨1490, op 0x52⟩,
  ⟨1491, .push 4 1352829926⟩,
  ⟨1496, .push 2 1728⟩,
  ⟨1499, op 0x52⟩,
  ⟨1500, .push 4 1548603684⟩,
  ⟨1505, .push 2 1760⟩,
  ⟨1508, op 0x52⟩,
  ⟨1509, .push 4 1836072691⟩,
  ⟨1514, .push 2 1792⟩,
  ⟨1517, op 0x52⟩,
  ⟨1518, .push 4 2053994217⟩,
  ⟨1523, .push 2 1824⟩,
  ⟨1526, op 0x52⟩,
  ⟨1527, .push 0 0⟩,
  ⟨1528, .push 2 1856⟩,
  ⟨1531, op 0x52⟩,
  ⟨1532, .push 4 1732584193⟩,
  ⟨1537, .push 1 32⟩,
  ⟨1539, op 0x52⟩,
  ⟨1540, .push 4 4023233417⟩,
  ⟨1545, .push 1 64⟩,
  ⟨1547, op 0x52⟩,
  ⟨1548, .push 4 2562383102⟩,
  ⟨1553, .push 1 96⟩,
  ⟨1555, op 0x52⟩,
  ⟨1556, .push 4 271733878⟩,
  ⟨1561, .push 1 128⟩,
  ⟨1563, op 0x52⟩,
  ⟨1564, .push 4 3285377520⟩,
  ⟨1569, .push 1 160⟩,
  ⟨1571, op 0x52⟩,
  ⟨1572, .push 2 1580⟩,
  ⟨1575, .push 0 0⟩,
  ⟨1576, .push 2 480⟩,
  ⟨1579, op 0x56⟩
]

@[simp] theorem indices_length : indices.length = 185 := by rfl
@[simp] theorem entries_length : entries.length = 185 := by rfl

end Challenge.Ripemd160.Reference.Proofs.Bytecode.ArtifactSnapshots
