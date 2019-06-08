--- before_pass
+++ after_pass
@@ -33,45 +33,33 @@ parser Parser(packet_in packet, out head
         }
     }
     state check_p4calc {
-        {
-            tmp = packet.lookahead<bit<128>>();
-            tmp_3.setValid();
-            {
-                tmp_3.p = tmp[127:120];
-                tmp_3.four = tmp[119:112];
-                tmp_3.ver = tmp[111:104];
-                tmp_3.op = tmp[103:96];
-                tmp_3.operand_a = tmp[95:64];
-                tmp_3.operand_b = tmp[63:32];
-                tmp_3.res = tmp[31:0];
-            }
-        }
-        {
-            tmp_0 = packet.lookahead<bit<128>>();
-            tmp_4.setValid();
-            {
-                tmp_4.p = tmp_0[127:120];
-                tmp_4.four = tmp_0[119:112];
-                tmp_4.ver = tmp_0[111:104];
-                tmp_4.op = tmp_0[103:96];
-                tmp_4.operand_a = tmp_0[95:64];
-                tmp_4.operand_b = tmp_0[63:32];
-                tmp_4.res = tmp_0[31:0];
-            }
-        }
-        {
-            tmp_1 = packet.lookahead<bit<128>>();
-            tmp_5.setValid();
-            {
-                tmp_5.p = tmp_1[127:120];
-                tmp_5.four = tmp_1[119:112];
-                tmp_5.ver = tmp_1[111:104];
-                tmp_5.op = tmp_1[103:96];
-                tmp_5.operand_a = tmp_1[95:64];
-                tmp_5.operand_b = tmp_1[63:32];
-                tmp_5.res = tmp_1[31:0];
-            }
-        }
+        tmp = packet.lookahead<bit<128>>();
+        tmp_3.setValid();
+        tmp_3.p = tmp[127:120];
+        tmp_3.four = tmp[119:112];
+        tmp_3.ver = tmp[111:104];
+        tmp_3.op = tmp[103:96];
+        tmp_3.operand_a = tmp[95:64];
+        tmp_3.operand_b = tmp[63:32];
+        tmp_3.res = tmp[31:0];
+        tmp_0 = packet.lookahead<bit<128>>();
+        tmp_4.setValid();
+        tmp_4.p = tmp_0[127:120];
+        tmp_4.four = tmp_0[119:112];
+        tmp_4.ver = tmp_0[111:104];
+        tmp_4.op = tmp_0[103:96];
+        tmp_4.operand_a = tmp_0[95:64];
+        tmp_4.operand_b = tmp_0[63:32];
+        tmp_4.res = tmp_0[31:0];
+        tmp_1 = packet.lookahead<bit<128>>();
+        tmp_5.setValid();
+        tmp_5.p = tmp_1[127:120];
+        tmp_5.four = tmp_1[119:112];
+        tmp_5.ver = tmp_1[111:104];
+        tmp_5.op = tmp_1[103:96];
+        tmp_5.operand_a = tmp_1[95:64];
+        tmp_5.operand_b = tmp_1[63:32];
+        tmp_5.res = tmp_1[31:0];
         transition select(tmp_3.p, tmp_4.four, tmp_5.ver) {
             (8w0x50, 8w0x34, 8w0x1): parse_p4calc;
             default: accept;
