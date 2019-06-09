--- before_pass
+++ after_pass
@@ -24,6 +24,9 @@ parser MyParser(packet_in packet, out he
     p4calc_t tmp;
     p4calc_t tmp_0;
     p4calc_t tmp_1;
+    bit<128> tmp_3;
+    bit<128> tmp_4;
+    bit<128> tmp_5;
     state start {
         packet.extract<ethernet_t>(hdr.ethernet);
         transition select(hdr.ethernet.etherType) {
@@ -32,9 +35,21 @@ parser MyParser(packet_in packet, out he
         }
     }
     state check_p4calc {
-        tmp = packet.lookahead<p4calc_t>();
-        tmp_0 = packet.lookahead<p4calc_t>();
-        tmp_1 = packet.lookahead<p4calc_t>();
+        {
+            tmp_3 = packet.lookahead<bit<128>>();
+            tmp.setValid();
+            tmp = {tmp_3[127:120],tmp_3[119:112],tmp_3[111:104],tmp_3[103:96],tmp_3[95:64],tmp_3[63:32],tmp_3[31:0]};
+        }
+        {
+            tmp_4 = packet.lookahead<bit<128>>();
+            tmp_0.setValid();
+            tmp_0 = {tmp_4[127:120],tmp_4[119:112],tmp_4[111:104],tmp_4[103:96],tmp_4[95:64],tmp_4[63:32],tmp_4[31:0]};
+        }
+        {
+            tmp_5 = packet.lookahead<bit<128>>();
+            tmp_1.setValid();
+            tmp_1 = {tmp_5[127:120],tmp_5[119:112],tmp_5[111:104],tmp_5[103:96],tmp_5[95:64],tmp_5[63:32],tmp_5[31:0]};
+        }
         transition select(tmp.p, tmp_0.four, tmp_1.ver) {
             (8w0x50, 8w0x34, 8w0x1): parse_p4calc;
             default: accept;
