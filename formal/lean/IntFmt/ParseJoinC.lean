/-
Copyright (C) Ahmad <ahmedparr93@gmail.com>
SPDX-License-Identifier: AGPL-3.0-only

Compose named parse/image chunk lemmas for lines 100–145 via
`parseDecText_append` and `extract_split`. Group results are
combined through named prefix definitions so Lean does not
reduce a long concatenation in a theorem type.
-/

import IntFmt.ParseJoinCore
import IntFmt.DecBindDataC

namespace IntFmt

set_option maxHeartbeats 800000
set_option maxRecDepth 20000

@[irreducible] def text_100_104 : String := decLine100 ++ decLine101 ++ decLine102 ++ decLine103 ++ decLine104
@[irreducible] def image_100_104 : Array UInt16 := ((((decChunk100 ++ decChunk101) ++ decChunk102) ++ decChunk103) ++ decChunk104)
private theorem ws_100_104_0 : listEndsWS decLine100.toList :=
  decLine100_ws
private theorem ws_100_104_1 : listEndsWS (decLine100 ++ decLine101).toList :=
  ws_cat (decLine100) decLine101 ws_100_104_0 decLine101_ws
private theorem ws_100_104_2 : listEndsWS (decLine100 ++ decLine101 ++ decLine102).toList :=
  ws_cat (decLine100 ++ decLine101) decLine102 ws_100_104_1 decLine102_ws
private theorem ws_100_104_3 : listEndsWS (decLine100 ++ decLine101 ++ decLine102 ++ decLine103).toList :=
  ws_cat (decLine100 ++ decLine101 ++ decLine102) decLine103 ws_100_104_2 decLine103_ws
private theorem ws_100_104_4 : listEndsWS (decLine100 ++ decLine101 ++ decLine102 ++ decLine103 ++ decLine104).toList :=
  ws_cat (decLine100 ++ decLine101 ++ decLine102 ++ decLine103) decLine104 ws_100_104_3 decLine104_ws
theorem parse_100_104 : parseDecText text_100_104 = image_100_104 := by
  have p1 := parse_append_eq decLine100 decLine101
    decChunk100 decChunk101
    ws_100_104_0 parse_line100 parse_line101
  have p2 := parse_append_eq (decLine100 ++ decLine101) decLine102
    (decChunk100 ++ decChunk101) decChunk102
    ws_100_104_1 p1 parse_line102
  have p3 := parse_append_eq (decLine100 ++ decLine101 ++ decLine102) decLine103
    ((decChunk100 ++ decChunk101) ++ decChunk102) decChunk103
    ws_100_104_2 p2 parse_line103
  have p4 := parse_append_eq (decLine100 ++ decLine101 ++ decLine102 ++ decLine103) decLine104
    (((decChunk100 ++ decChunk101) ++ decChunk102) ++ decChunk103) decChunk104
    ws_100_104_3 p3 parse_line104
  rw [text_100_104, image_100_104]
  exact p4
theorem extract_100_104 :
    intfmtImage.extract 1600 1680 = image_100_104 := by
  have i1 := extract_append_eq 1600 1616 1632
    decChunk100 decChunk101
    (by decide) (by decide) (by decide)
    image_chunk100 image_chunk101
  have i2 := extract_append_eq 1600 1632 1648
    (decChunk100 ++ decChunk101) decChunk102
    (by decide) (by decide) (by decide)
    i1 image_chunk102
  have i3 := extract_append_eq 1600 1648 1664
    ((decChunk100 ++ decChunk101) ++ decChunk102) decChunk103
    (by decide) (by decide) (by decide)
    i2 image_chunk103
  have i4 := extract_append_eq 1600 1664 1680
    (((decChunk100 ++ decChunk101) ++ decChunk102) ++ decChunk103) decChunk104
    (by decide) (by decide) (by decide)
    i3 image_chunk104
  rw [image_100_104]
  exact i4
private theorem ws_text_100_104 : listEndsWS text_100_104.toList := by
  unfold text_100_104
  exact ws_100_104_4

@[irreducible] def text_105_109 : String := decLine105 ++ decLine106 ++ decLine107 ++ decLine108 ++ decLine109
@[irreducible] def image_105_109 : Array UInt16 := ((((decChunk105 ++ decChunk106) ++ decChunk107) ++ decChunk108) ++ decChunk109)
private theorem ws_105_109_0 : listEndsWS decLine105.toList :=
  decLine105_ws
private theorem ws_105_109_1 : listEndsWS (decLine105 ++ decLine106).toList :=
  ws_cat (decLine105) decLine106 ws_105_109_0 decLine106_ws
private theorem ws_105_109_2 : listEndsWS (decLine105 ++ decLine106 ++ decLine107).toList :=
  ws_cat (decLine105 ++ decLine106) decLine107 ws_105_109_1 decLine107_ws
private theorem ws_105_109_3 : listEndsWS (decLine105 ++ decLine106 ++ decLine107 ++ decLine108).toList :=
  ws_cat (decLine105 ++ decLine106 ++ decLine107) decLine108 ws_105_109_2 decLine108_ws
private theorem ws_105_109_4 : listEndsWS (decLine105 ++ decLine106 ++ decLine107 ++ decLine108 ++ decLine109).toList :=
  ws_cat (decLine105 ++ decLine106 ++ decLine107 ++ decLine108) decLine109 ws_105_109_3 decLine109_ws
theorem parse_105_109 : parseDecText text_105_109 = image_105_109 := by
  have p1 := parse_append_eq decLine105 decLine106
    decChunk105 decChunk106
    ws_105_109_0 parse_line105 parse_line106
  have p2 := parse_append_eq (decLine105 ++ decLine106) decLine107
    (decChunk105 ++ decChunk106) decChunk107
    ws_105_109_1 p1 parse_line107
  have p3 := parse_append_eq (decLine105 ++ decLine106 ++ decLine107) decLine108
    ((decChunk105 ++ decChunk106) ++ decChunk107) decChunk108
    ws_105_109_2 p2 parse_line108
  have p4 := parse_append_eq (decLine105 ++ decLine106 ++ decLine107 ++ decLine108) decLine109
    (((decChunk105 ++ decChunk106) ++ decChunk107) ++ decChunk108) decChunk109
    ws_105_109_3 p3 parse_line109
  rw [text_105_109, image_105_109]
  exact p4
theorem extract_105_109 :
    intfmtImage.extract 1680 1760 = image_105_109 := by
  have i1 := extract_append_eq 1680 1696 1712
    decChunk105 decChunk106
    (by decide) (by decide) (by decide)
    image_chunk105 image_chunk106
  have i2 := extract_append_eq 1680 1712 1728
    (decChunk105 ++ decChunk106) decChunk107
    (by decide) (by decide) (by decide)
    i1 image_chunk107
  have i3 := extract_append_eq 1680 1728 1744
    ((decChunk105 ++ decChunk106) ++ decChunk107) decChunk108
    (by decide) (by decide) (by decide)
    i2 image_chunk108
  have i4 := extract_append_eq 1680 1744 1760
    (((decChunk105 ++ decChunk106) ++ decChunk107) ++ decChunk108) decChunk109
    (by decide) (by decide) (by decide)
    i3 image_chunk109
  rw [image_105_109]
  exact i4
private theorem ws_text_105_109 : listEndsWS text_105_109.toList := by
  unfold text_105_109
  exact ws_105_109_4

@[irreducible] def text_110_114 : String := decLine110 ++ decLine111 ++ decLine112 ++ decLine113 ++ decLine114
@[irreducible] def image_110_114 : Array UInt16 := ((((decChunk110 ++ decChunk111) ++ decChunk112) ++ decChunk113) ++ decChunk114)
private theorem ws_110_114_0 : listEndsWS decLine110.toList :=
  decLine110_ws
private theorem ws_110_114_1 : listEndsWS (decLine110 ++ decLine111).toList :=
  ws_cat (decLine110) decLine111 ws_110_114_0 decLine111_ws
private theorem ws_110_114_2 : listEndsWS (decLine110 ++ decLine111 ++ decLine112).toList :=
  ws_cat (decLine110 ++ decLine111) decLine112 ws_110_114_1 decLine112_ws
private theorem ws_110_114_3 : listEndsWS (decLine110 ++ decLine111 ++ decLine112 ++ decLine113).toList :=
  ws_cat (decLine110 ++ decLine111 ++ decLine112) decLine113 ws_110_114_2 decLine113_ws
private theorem ws_110_114_4 : listEndsWS (decLine110 ++ decLine111 ++ decLine112 ++ decLine113 ++ decLine114).toList :=
  ws_cat (decLine110 ++ decLine111 ++ decLine112 ++ decLine113) decLine114 ws_110_114_3 decLine114_ws
theorem parse_110_114 : parseDecText text_110_114 = image_110_114 := by
  have p1 := parse_append_eq decLine110 decLine111
    decChunk110 decChunk111
    ws_110_114_0 parse_line110 parse_line111
  have p2 := parse_append_eq (decLine110 ++ decLine111) decLine112
    (decChunk110 ++ decChunk111) decChunk112
    ws_110_114_1 p1 parse_line112
  have p3 := parse_append_eq (decLine110 ++ decLine111 ++ decLine112) decLine113
    ((decChunk110 ++ decChunk111) ++ decChunk112) decChunk113
    ws_110_114_2 p2 parse_line113
  have p4 := parse_append_eq (decLine110 ++ decLine111 ++ decLine112 ++ decLine113) decLine114
    (((decChunk110 ++ decChunk111) ++ decChunk112) ++ decChunk113) decChunk114
    ws_110_114_3 p3 parse_line114
  rw [text_110_114, image_110_114]
  exact p4
theorem extract_110_114 :
    intfmtImage.extract 1760 1840 = image_110_114 := by
  have i1 := extract_append_eq 1760 1776 1792
    decChunk110 decChunk111
    (by decide) (by decide) (by decide)
    image_chunk110 image_chunk111
  have i2 := extract_append_eq 1760 1792 1808
    (decChunk110 ++ decChunk111) decChunk112
    (by decide) (by decide) (by decide)
    i1 image_chunk112
  have i3 := extract_append_eq 1760 1808 1824
    ((decChunk110 ++ decChunk111) ++ decChunk112) decChunk113
    (by decide) (by decide) (by decide)
    i2 image_chunk113
  have i4 := extract_append_eq 1760 1824 1840
    (((decChunk110 ++ decChunk111) ++ decChunk112) ++ decChunk113) decChunk114
    (by decide) (by decide) (by decide)
    i3 image_chunk114
  rw [image_110_114]
  exact i4
private theorem ws_text_110_114 : listEndsWS text_110_114.toList := by
  unfold text_110_114
  exact ws_110_114_4

@[irreducible] def text_115_119 : String := decLine115 ++ decLine116 ++ decLine117 ++ decLine118 ++ decLine119
@[irreducible] def image_115_119 : Array UInt16 := ((((decChunk115 ++ decChunk116) ++ decChunk117) ++ decChunk118) ++ decChunk119)
private theorem ws_115_119_0 : listEndsWS decLine115.toList :=
  decLine115_ws
private theorem ws_115_119_1 : listEndsWS (decLine115 ++ decLine116).toList :=
  ws_cat (decLine115) decLine116 ws_115_119_0 decLine116_ws
private theorem ws_115_119_2 : listEndsWS (decLine115 ++ decLine116 ++ decLine117).toList :=
  ws_cat (decLine115 ++ decLine116) decLine117 ws_115_119_1 decLine117_ws
private theorem ws_115_119_3 : listEndsWS (decLine115 ++ decLine116 ++ decLine117 ++ decLine118).toList :=
  ws_cat (decLine115 ++ decLine116 ++ decLine117) decLine118 ws_115_119_2 decLine118_ws
private theorem ws_115_119_4 : listEndsWS (decLine115 ++ decLine116 ++ decLine117 ++ decLine118 ++ decLine119).toList :=
  ws_cat (decLine115 ++ decLine116 ++ decLine117 ++ decLine118) decLine119 ws_115_119_3 decLine119_ws
theorem parse_115_119 : parseDecText text_115_119 = image_115_119 := by
  have p1 := parse_append_eq decLine115 decLine116
    decChunk115 decChunk116
    ws_115_119_0 parse_line115 parse_line116
  have p2 := parse_append_eq (decLine115 ++ decLine116) decLine117
    (decChunk115 ++ decChunk116) decChunk117
    ws_115_119_1 p1 parse_line117
  have p3 := parse_append_eq (decLine115 ++ decLine116 ++ decLine117) decLine118
    ((decChunk115 ++ decChunk116) ++ decChunk117) decChunk118
    ws_115_119_2 p2 parse_line118
  have p4 := parse_append_eq (decLine115 ++ decLine116 ++ decLine117 ++ decLine118) decLine119
    (((decChunk115 ++ decChunk116) ++ decChunk117) ++ decChunk118) decChunk119
    ws_115_119_3 p3 parse_line119
  rw [text_115_119, image_115_119]
  exact p4
theorem extract_115_119 :
    intfmtImage.extract 1840 1920 = image_115_119 := by
  have i1 := extract_append_eq 1840 1856 1872
    decChunk115 decChunk116
    (by decide) (by decide) (by decide)
    image_chunk115 image_chunk116
  have i2 := extract_append_eq 1840 1872 1888
    (decChunk115 ++ decChunk116) decChunk117
    (by decide) (by decide) (by decide)
    i1 image_chunk117
  have i3 := extract_append_eq 1840 1888 1904
    ((decChunk115 ++ decChunk116) ++ decChunk117) decChunk118
    (by decide) (by decide) (by decide)
    i2 image_chunk118
  have i4 := extract_append_eq 1840 1904 1920
    (((decChunk115 ++ decChunk116) ++ decChunk117) ++ decChunk118) decChunk119
    (by decide) (by decide) (by decide)
    i3 image_chunk119
  rw [image_115_119]
  exact i4
private theorem ws_text_115_119 : listEndsWS text_115_119.toList := by
  unfold text_115_119
  exact ws_115_119_4

@[irreducible] def text_120_124 : String := decLine120 ++ decLine121 ++ decLine122 ++ decLine123 ++ decLine124
@[irreducible] def image_120_124 : Array UInt16 := ((((decChunk120 ++ decChunk121) ++ decChunk122) ++ decChunk123) ++ decChunk124)
private theorem ws_120_124_0 : listEndsWS decLine120.toList :=
  decLine120_ws
private theorem ws_120_124_1 : listEndsWS (decLine120 ++ decLine121).toList :=
  ws_cat (decLine120) decLine121 ws_120_124_0 decLine121_ws
private theorem ws_120_124_2 : listEndsWS (decLine120 ++ decLine121 ++ decLine122).toList :=
  ws_cat (decLine120 ++ decLine121) decLine122 ws_120_124_1 decLine122_ws
private theorem ws_120_124_3 : listEndsWS (decLine120 ++ decLine121 ++ decLine122 ++ decLine123).toList :=
  ws_cat (decLine120 ++ decLine121 ++ decLine122) decLine123 ws_120_124_2 decLine123_ws
private theorem ws_120_124_4 : listEndsWS (decLine120 ++ decLine121 ++ decLine122 ++ decLine123 ++ decLine124).toList :=
  ws_cat (decLine120 ++ decLine121 ++ decLine122 ++ decLine123) decLine124 ws_120_124_3 decLine124_ws
theorem parse_120_124 : parseDecText text_120_124 = image_120_124 := by
  have p1 := parse_append_eq decLine120 decLine121
    decChunk120 decChunk121
    ws_120_124_0 parse_line120 parse_line121
  have p2 := parse_append_eq (decLine120 ++ decLine121) decLine122
    (decChunk120 ++ decChunk121) decChunk122
    ws_120_124_1 p1 parse_line122
  have p3 := parse_append_eq (decLine120 ++ decLine121 ++ decLine122) decLine123
    ((decChunk120 ++ decChunk121) ++ decChunk122) decChunk123
    ws_120_124_2 p2 parse_line123
  have p4 := parse_append_eq (decLine120 ++ decLine121 ++ decLine122 ++ decLine123) decLine124
    (((decChunk120 ++ decChunk121) ++ decChunk122) ++ decChunk123) decChunk124
    ws_120_124_3 p3 parse_line124
  rw [text_120_124, image_120_124]
  exact p4
theorem extract_120_124 :
    intfmtImage.extract 1920 2000 = image_120_124 := by
  have i1 := extract_append_eq 1920 1936 1952
    decChunk120 decChunk121
    (by decide) (by decide) (by decide)
    image_chunk120 image_chunk121
  have i2 := extract_append_eq 1920 1952 1968
    (decChunk120 ++ decChunk121) decChunk122
    (by decide) (by decide) (by decide)
    i1 image_chunk122
  have i3 := extract_append_eq 1920 1968 1984
    ((decChunk120 ++ decChunk121) ++ decChunk122) decChunk123
    (by decide) (by decide) (by decide)
    i2 image_chunk123
  have i4 := extract_append_eq 1920 1984 2000
    (((decChunk120 ++ decChunk121) ++ decChunk122) ++ decChunk123) decChunk124
    (by decide) (by decide) (by decide)
    i3 image_chunk124
  rw [image_120_124]
  exact i4
private theorem ws_text_120_124 : listEndsWS text_120_124.toList := by
  unfold text_120_124
  exact ws_120_124_4

@[irreducible] def text_125_129 : String := decLine125 ++ decLine126 ++ decLine127 ++ decLine128 ++ decLine129
@[irreducible] def image_125_129 : Array UInt16 := ((((decChunk125 ++ decChunk126) ++ decChunk127) ++ decChunk128) ++ decChunk129)
private theorem ws_125_129_0 : listEndsWS decLine125.toList :=
  decLine125_ws
private theorem ws_125_129_1 : listEndsWS (decLine125 ++ decLine126).toList :=
  ws_cat (decLine125) decLine126 ws_125_129_0 decLine126_ws
private theorem ws_125_129_2 : listEndsWS (decLine125 ++ decLine126 ++ decLine127).toList :=
  ws_cat (decLine125 ++ decLine126) decLine127 ws_125_129_1 decLine127_ws
private theorem ws_125_129_3 : listEndsWS (decLine125 ++ decLine126 ++ decLine127 ++ decLine128).toList :=
  ws_cat (decLine125 ++ decLine126 ++ decLine127) decLine128 ws_125_129_2 decLine128_ws
private theorem ws_125_129_4 : listEndsWS (decLine125 ++ decLine126 ++ decLine127 ++ decLine128 ++ decLine129).toList :=
  ws_cat (decLine125 ++ decLine126 ++ decLine127 ++ decLine128) decLine129 ws_125_129_3 decLine129_ws
theorem parse_125_129 : parseDecText text_125_129 = image_125_129 := by
  have p1 := parse_append_eq decLine125 decLine126
    decChunk125 decChunk126
    ws_125_129_0 parse_line125 parse_line126
  have p2 := parse_append_eq (decLine125 ++ decLine126) decLine127
    (decChunk125 ++ decChunk126) decChunk127
    ws_125_129_1 p1 parse_line127
  have p3 := parse_append_eq (decLine125 ++ decLine126 ++ decLine127) decLine128
    ((decChunk125 ++ decChunk126) ++ decChunk127) decChunk128
    ws_125_129_2 p2 parse_line128
  have p4 := parse_append_eq (decLine125 ++ decLine126 ++ decLine127 ++ decLine128) decLine129
    (((decChunk125 ++ decChunk126) ++ decChunk127) ++ decChunk128) decChunk129
    ws_125_129_3 p3 parse_line129
  rw [text_125_129, image_125_129]
  exact p4
theorem extract_125_129 :
    intfmtImage.extract 2000 2080 = image_125_129 := by
  have i1 := extract_append_eq 2000 2016 2032
    decChunk125 decChunk126
    (by decide) (by decide) (by decide)
    image_chunk125 image_chunk126
  have i2 := extract_append_eq 2000 2032 2048
    (decChunk125 ++ decChunk126) decChunk127
    (by decide) (by decide) (by decide)
    i1 image_chunk127
  have i3 := extract_append_eq 2000 2048 2064
    ((decChunk125 ++ decChunk126) ++ decChunk127) decChunk128
    (by decide) (by decide) (by decide)
    i2 image_chunk128
  have i4 := extract_append_eq 2000 2064 2080
    (((decChunk125 ++ decChunk126) ++ decChunk127) ++ decChunk128) decChunk129
    (by decide) (by decide) (by decide)
    i3 image_chunk129
  rw [image_125_129]
  exact i4
private theorem ws_text_125_129 : listEndsWS text_125_129.toList := by
  unfold text_125_129
  exact ws_125_129_4

@[irreducible] def text_130_134 : String := decLine130 ++ decLine131 ++ decLine132 ++ decLine133 ++ decLine134
@[irreducible] def image_130_134 : Array UInt16 := ((((decChunk130 ++ decChunk131) ++ decChunk132) ++ decChunk133) ++ decChunk134)
private theorem ws_130_134_0 : listEndsWS decLine130.toList :=
  decLine130_ws
private theorem ws_130_134_1 : listEndsWS (decLine130 ++ decLine131).toList :=
  ws_cat (decLine130) decLine131 ws_130_134_0 decLine131_ws
private theorem ws_130_134_2 : listEndsWS (decLine130 ++ decLine131 ++ decLine132).toList :=
  ws_cat (decLine130 ++ decLine131) decLine132 ws_130_134_1 decLine132_ws
private theorem ws_130_134_3 : listEndsWS (decLine130 ++ decLine131 ++ decLine132 ++ decLine133).toList :=
  ws_cat (decLine130 ++ decLine131 ++ decLine132) decLine133 ws_130_134_2 decLine133_ws
private theorem ws_130_134_4 : listEndsWS (decLine130 ++ decLine131 ++ decLine132 ++ decLine133 ++ decLine134).toList :=
  ws_cat (decLine130 ++ decLine131 ++ decLine132 ++ decLine133) decLine134 ws_130_134_3 decLine134_ws
theorem parse_130_134 : parseDecText text_130_134 = image_130_134 := by
  have p1 := parse_append_eq decLine130 decLine131
    decChunk130 decChunk131
    ws_130_134_0 parse_line130 parse_line131
  have p2 := parse_append_eq (decLine130 ++ decLine131) decLine132
    (decChunk130 ++ decChunk131) decChunk132
    ws_130_134_1 p1 parse_line132
  have p3 := parse_append_eq (decLine130 ++ decLine131 ++ decLine132) decLine133
    ((decChunk130 ++ decChunk131) ++ decChunk132) decChunk133
    ws_130_134_2 p2 parse_line133
  have p4 := parse_append_eq (decLine130 ++ decLine131 ++ decLine132 ++ decLine133) decLine134
    (((decChunk130 ++ decChunk131) ++ decChunk132) ++ decChunk133) decChunk134
    ws_130_134_3 p3 parse_line134
  rw [text_130_134, image_130_134]
  exact p4
theorem extract_130_134 :
    intfmtImage.extract 2080 2160 = image_130_134 := by
  have i1 := extract_append_eq 2080 2096 2112
    decChunk130 decChunk131
    (by decide) (by decide) (by decide)
    image_chunk130 image_chunk131
  have i2 := extract_append_eq 2080 2112 2128
    (decChunk130 ++ decChunk131) decChunk132
    (by decide) (by decide) (by decide)
    i1 image_chunk132
  have i3 := extract_append_eq 2080 2128 2144
    ((decChunk130 ++ decChunk131) ++ decChunk132) decChunk133
    (by decide) (by decide) (by decide)
    i2 image_chunk133
  have i4 := extract_append_eq 2080 2144 2160
    (((decChunk130 ++ decChunk131) ++ decChunk132) ++ decChunk133) decChunk134
    (by decide) (by decide) (by decide)
    i3 image_chunk134
  rw [image_130_134]
  exact i4
private theorem ws_text_130_134 : listEndsWS text_130_134.toList := by
  unfold text_130_134
  exact ws_130_134_4

@[irreducible] def text_135_139 : String := decLine135 ++ decLine136 ++ decLine137 ++ decLine138 ++ decLine139
@[irreducible] def image_135_139 : Array UInt16 := ((((decChunk135 ++ decChunk136) ++ decChunk137) ++ decChunk138) ++ decChunk139)
private theorem ws_135_139_0 : listEndsWS decLine135.toList :=
  decLine135_ws
private theorem ws_135_139_1 : listEndsWS (decLine135 ++ decLine136).toList :=
  ws_cat (decLine135) decLine136 ws_135_139_0 decLine136_ws
private theorem ws_135_139_2 : listEndsWS (decLine135 ++ decLine136 ++ decLine137).toList :=
  ws_cat (decLine135 ++ decLine136) decLine137 ws_135_139_1 decLine137_ws
private theorem ws_135_139_3 : listEndsWS (decLine135 ++ decLine136 ++ decLine137 ++ decLine138).toList :=
  ws_cat (decLine135 ++ decLine136 ++ decLine137) decLine138 ws_135_139_2 decLine138_ws
private theorem ws_135_139_4 : listEndsWS (decLine135 ++ decLine136 ++ decLine137 ++ decLine138 ++ decLine139).toList :=
  ws_cat (decLine135 ++ decLine136 ++ decLine137 ++ decLine138) decLine139 ws_135_139_3 decLine139_ws
theorem parse_135_139 : parseDecText text_135_139 = image_135_139 := by
  have p1 := parse_append_eq decLine135 decLine136
    decChunk135 decChunk136
    ws_135_139_0 parse_line135 parse_line136
  have p2 := parse_append_eq (decLine135 ++ decLine136) decLine137
    (decChunk135 ++ decChunk136) decChunk137
    ws_135_139_1 p1 parse_line137
  have p3 := parse_append_eq (decLine135 ++ decLine136 ++ decLine137) decLine138
    ((decChunk135 ++ decChunk136) ++ decChunk137) decChunk138
    ws_135_139_2 p2 parse_line138
  have p4 := parse_append_eq (decLine135 ++ decLine136 ++ decLine137 ++ decLine138) decLine139
    (((decChunk135 ++ decChunk136) ++ decChunk137) ++ decChunk138) decChunk139
    ws_135_139_3 p3 parse_line139
  rw [text_135_139, image_135_139]
  exact p4
theorem extract_135_139 :
    intfmtImage.extract 2160 2240 = image_135_139 := by
  have i1 := extract_append_eq 2160 2176 2192
    decChunk135 decChunk136
    (by decide) (by decide) (by decide)
    image_chunk135 image_chunk136
  have i2 := extract_append_eq 2160 2192 2208
    (decChunk135 ++ decChunk136) decChunk137
    (by decide) (by decide) (by decide)
    i1 image_chunk137
  have i3 := extract_append_eq 2160 2208 2224
    ((decChunk135 ++ decChunk136) ++ decChunk137) decChunk138
    (by decide) (by decide) (by decide)
    i2 image_chunk138
  have i4 := extract_append_eq 2160 2224 2240
    (((decChunk135 ++ decChunk136) ++ decChunk137) ++ decChunk138) decChunk139
    (by decide) (by decide) (by decide)
    i3 image_chunk139
  rw [image_135_139]
  exact i4
private theorem ws_text_135_139 : listEndsWS text_135_139.toList := by
  unfold text_135_139
  exact ws_135_139_4

@[irreducible] def text_140_145 : String := decLine140 ++ decLine141 ++ decLine142 ++ decLine143 ++ decLine144 ++ decLine145
@[irreducible] def image_140_145 : Array UInt16 := (((((decChunk140 ++ decChunk141) ++ decChunk142) ++ decChunk143) ++ decChunk144) ++ decChunk145)
private theorem ws_140_145_0 : listEndsWS decLine140.toList :=
  decLine140_ws
private theorem ws_140_145_1 : listEndsWS (decLine140 ++ decLine141).toList :=
  ws_cat (decLine140) decLine141 ws_140_145_0 decLine141_ws
private theorem ws_140_145_2 : listEndsWS (decLine140 ++ decLine141 ++ decLine142).toList :=
  ws_cat (decLine140 ++ decLine141) decLine142 ws_140_145_1 decLine142_ws
private theorem ws_140_145_3 : listEndsWS (decLine140 ++ decLine141 ++ decLine142 ++ decLine143).toList :=
  ws_cat (decLine140 ++ decLine141 ++ decLine142) decLine143 ws_140_145_2 decLine143_ws
private theorem ws_140_145_4 : listEndsWS (decLine140 ++ decLine141 ++ decLine142 ++ decLine143 ++ decLine144).toList :=
  ws_cat (decLine140 ++ decLine141 ++ decLine142 ++ decLine143) decLine144 ws_140_145_3 decLine144_ws
private theorem ws_140_145_5 : listEndsWS (decLine140 ++ decLine141 ++ decLine142 ++ decLine143 ++ decLine144 ++ decLine145).toList :=
  ws_cat (decLine140 ++ decLine141 ++ decLine142 ++ decLine143 ++ decLine144) decLine145 ws_140_145_4 decLine145_ws
theorem parse_140_145 : parseDecText text_140_145 = image_140_145 := by
  have p1 := parse_append_eq decLine140 decLine141
    decChunk140 decChunk141
    ws_140_145_0 parse_line140 parse_line141
  have p2 := parse_append_eq (decLine140 ++ decLine141) decLine142
    (decChunk140 ++ decChunk141) decChunk142
    ws_140_145_1 p1 parse_line142
  have p3 := parse_append_eq (decLine140 ++ decLine141 ++ decLine142) decLine143
    ((decChunk140 ++ decChunk141) ++ decChunk142) decChunk143
    ws_140_145_2 p2 parse_line143
  have p4 := parse_append_eq (decLine140 ++ decLine141 ++ decLine142 ++ decLine143) decLine144
    (((decChunk140 ++ decChunk141) ++ decChunk142) ++ decChunk143) decChunk144
    ws_140_145_3 p3 parse_line144
  have p5 := parse_append_eq (decLine140 ++ decLine141 ++ decLine142 ++ decLine143 ++ decLine144) decLine145
    ((((decChunk140 ++ decChunk141) ++ decChunk142) ++ decChunk143) ++ decChunk144) decChunk145
    ws_140_145_4 p4 parse_line145
  rw [text_140_145, image_140_145]
  exact p5
theorem extract_140_145 :
    intfmtImage.extract 2240 2323 = image_140_145 := by
  have i1 := extract_append_eq 2240 2256 2272
    decChunk140 decChunk141
    (by decide) (by decide) (by decide)
    image_chunk140 image_chunk141
  have i2 := extract_append_eq 2240 2272 2288
    (decChunk140 ++ decChunk141) decChunk142
    (by decide) (by decide) (by decide)
    i1 image_chunk142
  have i3 := extract_append_eq 2240 2288 2304
    ((decChunk140 ++ decChunk141) ++ decChunk142) decChunk143
    (by decide) (by decide) (by decide)
    i2 image_chunk143
  have i4 := extract_append_eq 2240 2304 2320
    (((decChunk140 ++ decChunk141) ++ decChunk142) ++ decChunk143) decChunk144
    (by decide) (by decide) (by decide)
    i3 image_chunk144
  have i5 := extract_append_eq 2240 2320 2323
    ((((decChunk140 ++ decChunk141) ++ decChunk142) ++ decChunk143) ++ decChunk144) decChunk145
    (by decide) (by decide) (by decide)
    i4 image_chunk145
  rw [image_140_145]
  exact i5
private theorem ws_text_140_145 : listEndsWS text_140_145.toList := by
  unfold text_140_145
  exact ws_140_145_5

@[irreducible] def joinC_pref1 : String := text_100_104 ++ text_105_109
@[irreducible] def joinC_img1 : Array UInt16 := image_100_104 ++ image_105_109
private theorem ws_joinC_pref1 : listEndsWS joinC_pref1.toList := by
  unfold joinC_pref1
  exact ws_cat text_100_104 text_105_109 ws_text_100_104 ws_text_105_109
theorem parse_joinC_pref1 :
    parseDecText joinC_pref1 = joinC_img1 := by
  have h := parse_append_eq text_100_104 text_105_109 image_100_104 image_105_109
    ws_text_100_104 parse_100_104 parse_105_109
  unfold joinC_pref1 joinC_img1
  exact h
theorem extract_joinC_pref1 :
    intfmtImage.extract 1600 1760 = joinC_img1 := by
  have h := extract_append_eq 1600 1680 1760 image_100_104 image_105_109
    (by decide) (by decide) (by decide)
    extract_100_104 extract_105_109
  unfold joinC_img1
  exact h
@[irreducible] def joinC_pref2 : String := joinC_pref1 ++ text_110_114
@[irreducible] def joinC_img2 : Array UInt16 := joinC_img1 ++ image_110_114
private theorem ws_joinC_pref2 : listEndsWS joinC_pref2.toList := by
  unfold joinC_pref2
  exact ws_cat joinC_pref1 text_110_114 ws_joinC_pref1 ws_text_110_114
theorem parse_joinC_pref2 :
    parseDecText joinC_pref2 = joinC_img2 := by
  have h := parse_append_eq joinC_pref1 text_110_114
    joinC_img1 image_110_114
    ws_joinC_pref1 parse_joinC_pref1 parse_110_114
  unfold joinC_pref2 joinC_img2
  exact h
theorem extract_joinC_pref2 :
    intfmtImage.extract 1600 1840 = joinC_img2 := by
  have h := extract_append_eq 1600 1760 1840
    joinC_img1 image_110_114
    (by decide) (by decide) (by decide)
    extract_joinC_pref1 extract_110_114
  unfold joinC_img2
  exact h
@[irreducible] def joinC_pref3 : String := joinC_pref2 ++ text_115_119
@[irreducible] def joinC_img3 : Array UInt16 := joinC_img2 ++ image_115_119
private theorem ws_joinC_pref3 : listEndsWS joinC_pref3.toList := by
  unfold joinC_pref3
  exact ws_cat joinC_pref2 text_115_119 ws_joinC_pref2 ws_text_115_119
theorem parse_joinC_pref3 :
    parseDecText joinC_pref3 = joinC_img3 := by
  have h := parse_append_eq joinC_pref2 text_115_119
    joinC_img2 image_115_119
    ws_joinC_pref2 parse_joinC_pref2 parse_115_119
  unfold joinC_pref3 joinC_img3
  exact h
theorem extract_joinC_pref3 :
    intfmtImage.extract 1600 1920 = joinC_img3 := by
  have h := extract_append_eq 1600 1840 1920
    joinC_img2 image_115_119
    (by decide) (by decide) (by decide)
    extract_joinC_pref2 extract_115_119
  unfold joinC_img3
  exact h
@[irreducible] def joinC_pref4 : String := joinC_pref3 ++ text_120_124
@[irreducible] def joinC_img4 : Array UInt16 := joinC_img3 ++ image_120_124
private theorem ws_joinC_pref4 : listEndsWS joinC_pref4.toList := by
  unfold joinC_pref4
  exact ws_cat joinC_pref3 text_120_124 ws_joinC_pref3 ws_text_120_124
theorem parse_joinC_pref4 :
    parseDecText joinC_pref4 = joinC_img4 := by
  have h := parse_append_eq joinC_pref3 text_120_124
    joinC_img3 image_120_124
    ws_joinC_pref3 parse_joinC_pref3 parse_120_124
  unfold joinC_pref4 joinC_img4
  exact h
theorem extract_joinC_pref4 :
    intfmtImage.extract 1600 2000 = joinC_img4 := by
  have h := extract_append_eq 1600 1920 2000
    joinC_img3 image_120_124
    (by decide) (by decide) (by decide)
    extract_joinC_pref3 extract_120_124
  unfold joinC_img4
  exact h
@[irreducible] def joinC_pref5 : String := joinC_pref4 ++ text_125_129
@[irreducible] def joinC_img5 : Array UInt16 := joinC_img4 ++ image_125_129
private theorem ws_joinC_pref5 : listEndsWS joinC_pref5.toList := by
  unfold joinC_pref5
  exact ws_cat joinC_pref4 text_125_129 ws_joinC_pref4 ws_text_125_129
theorem parse_joinC_pref5 :
    parseDecText joinC_pref5 = joinC_img5 := by
  have h := parse_append_eq joinC_pref4 text_125_129
    joinC_img4 image_125_129
    ws_joinC_pref4 parse_joinC_pref4 parse_125_129
  unfold joinC_pref5 joinC_img5
  exact h
theorem extract_joinC_pref5 :
    intfmtImage.extract 1600 2080 = joinC_img5 := by
  have h := extract_append_eq 1600 2000 2080
    joinC_img4 image_125_129
    (by decide) (by decide) (by decide)
    extract_joinC_pref4 extract_125_129
  unfold joinC_img5
  exact h
@[irreducible] def joinC_pref6 : String := joinC_pref5 ++ text_130_134
@[irreducible] def joinC_img6 : Array UInt16 := joinC_img5 ++ image_130_134
private theorem ws_joinC_pref6 : listEndsWS joinC_pref6.toList := by
  unfold joinC_pref6
  exact ws_cat joinC_pref5 text_130_134 ws_joinC_pref5 ws_text_130_134
theorem parse_joinC_pref6 :
    parseDecText joinC_pref6 = joinC_img6 := by
  have h := parse_append_eq joinC_pref5 text_130_134
    joinC_img5 image_130_134
    ws_joinC_pref5 parse_joinC_pref5 parse_130_134
  unfold joinC_pref6 joinC_img6
  exact h
theorem extract_joinC_pref6 :
    intfmtImage.extract 1600 2160 = joinC_img6 := by
  have h := extract_append_eq 1600 2080 2160
    joinC_img5 image_130_134
    (by decide) (by decide) (by decide)
    extract_joinC_pref5 extract_130_134
  unfold joinC_img6
  exact h
@[irreducible] def joinC_pref7 : String := joinC_pref6 ++ text_135_139
@[irreducible] def joinC_img7 : Array UInt16 := joinC_img6 ++ image_135_139
private theorem ws_joinC_pref7 : listEndsWS joinC_pref7.toList := by
  unfold joinC_pref7
  exact ws_cat joinC_pref6 text_135_139 ws_joinC_pref6 ws_text_135_139
theorem parse_joinC_pref7 :
    parseDecText joinC_pref7 = joinC_img7 := by
  have h := parse_append_eq joinC_pref6 text_135_139
    joinC_img6 image_135_139
    ws_joinC_pref6 parse_joinC_pref6 parse_135_139
  unfold joinC_pref7 joinC_img7
  exact h
theorem extract_joinC_pref7 :
    intfmtImage.extract 1600 2240 = joinC_img7 := by
  have h := extract_append_eq 1600 2160 2240
    joinC_img6 image_135_139
    (by decide) (by decide) (by decide)
    extract_joinC_pref6 extract_135_139
  unfold joinC_img7
  exact h
@[irreducible] def joinC_pref8 : String := joinC_pref7 ++ text_140_145
@[irreducible] def joinC_img8 : Array UInt16 := joinC_img7 ++ image_140_145
private theorem ws_joinC_pref8 : listEndsWS joinC_pref8.toList := by
  unfold joinC_pref8
  exact ws_cat joinC_pref7 text_140_145 ws_joinC_pref7 ws_text_140_145
theorem parse_joinC_pref8 :
    parseDecText joinC_pref8 = joinC_img8 := by
  have h := parse_append_eq joinC_pref7 text_140_145
    joinC_img7 image_140_145
    ws_joinC_pref7 parse_joinC_pref7 parse_140_145
  unfold joinC_pref8 joinC_img8
  exact h
theorem extract_joinC_pref8 :
    intfmtImage.extract 1600 2323 = joinC_img8 := by
  have h := extract_append_eq 1600 2240 2323
    joinC_img7 image_140_145
    (by decide) (by decide) (by decide)
    extract_joinC_pref7 extract_140_145
  unfold joinC_img8
  exact h
@[irreducible] def joinCText : String := joinC_pref8
@[irreducible] def joinCImage : Array UInt16 := joinC_img8
theorem parse_joinC : parseDecText joinCText = joinCImage := by
  unfold joinCText joinCImage
  exact parse_joinC_pref8
theorem extract_joinC :
    intfmtImage.extract 1600 2323 = joinCImage := by
  unfold joinCImage
  exact extract_joinC_pref8
theorem ws_joinC : listEndsWS joinCText.toList := by
  unfold joinCText
  exact ws_joinC_pref8

end IntFmt
