--- before_pass
+++ after_pass
@@ -72,7 +72,7 @@ parser Parser(packet_in packet, out head
                 tmp_1.res = tmp_5[31:0];
             }
         }
-        transition select(tmp.p, tmp_0.four, tmp_1.ver) {
+        transition select(tmp_3[127:120], tmp_4[119:112], tmp_5[111:104]) {
             (8w0x50, 8w0x34, 8w0x1): parse_p4calc;
             default: accept;
         }
