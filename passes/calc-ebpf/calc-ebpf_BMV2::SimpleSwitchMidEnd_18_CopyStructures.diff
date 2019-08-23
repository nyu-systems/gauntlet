--- before_pass
+++ after_pass
@@ -36,17 +36,41 @@ parser Parser(packet_in packet, out head
         {
             tmp_3 = packet.lookahead<bit<128>>();
             tmp.setValid();
-            tmp = p4calc_t {p = tmp_3[127:120],four = tmp_3[119:112],ver = tmp_3[111:104],op = tmp_3[103:96],operand_a = tmp_3[95:64],operand_b = tmp_3[63:32],res = tmp_3[31:0]};
+            {
+                tmp.p = tmp_3[127:120];
+                tmp.four = tmp_3[119:112];
+                tmp.ver = tmp_3[111:104];
+                tmp.op = tmp_3[103:96];
+                tmp.operand_a = tmp_3[95:64];
+                tmp.operand_b = tmp_3[63:32];
+                tmp.res = tmp_3[31:0];
+            }
         }
         {
             tmp_4 = packet.lookahead<bit<128>>();
             tmp_0.setValid();
-            tmp_0 = p4calc_t {p = tmp_4[127:120],four = tmp_4[119:112],ver = tmp_4[111:104],op = tmp_4[103:96],operand_a = tmp_4[95:64],operand_b = tmp_4[63:32],res = tmp_4[31:0]};
+            {
+                tmp_0.p = tmp_4[127:120];
+                tmp_0.four = tmp_4[119:112];
+                tmp_0.ver = tmp_4[111:104];
+                tmp_0.op = tmp_4[103:96];
+                tmp_0.operand_a = tmp_4[95:64];
+                tmp_0.operand_b = tmp_4[63:32];
+                tmp_0.res = tmp_4[31:0];
+            }
         }
         {
             tmp_5 = packet.lookahead<bit<128>>();
             tmp_1.setValid();
-            tmp_1 = p4calc_t {p = tmp_5[127:120],four = tmp_5[119:112],ver = tmp_5[111:104],op = tmp_5[103:96],operand_a = tmp_5[95:64],operand_b = tmp_5[63:32],res = tmp_5[31:0]};
+            {
+                tmp_1.p = tmp_5[127:120];
+                tmp_1.four = tmp_5[119:112];
+                tmp_1.ver = tmp_5[111:104];
+                tmp_1.op = tmp_5[103:96];
+                tmp_1.operand_a = tmp_5[95:64];
+                tmp_1.operand_b = tmp_5[63:32];
+                tmp_1.res = tmp_5[31:0];
+            }
         }
         transition select(tmp.p, tmp_0.four, tmp_1.ver) {
             (8w0x50, 8w0x34, 8w0x1): parse_p4calc;
