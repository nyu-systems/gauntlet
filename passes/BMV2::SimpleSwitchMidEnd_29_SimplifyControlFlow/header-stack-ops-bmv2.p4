--- before_pass
+++ after_pass
@@ -56,11 +56,7 @@ parser parserI(packet_in pkt, out header
 control cIngress(inout headers hdr, inout metadata meta, inout standard_metadata_t stdmeta) {
     h2_t[5] hdr_1_h2;
     apply {
-        {
-        }
-        {
-            hdr_1_h2 = hdr.h2;
-        }
+        hdr_1_h2 = hdr.h2;
         if (hdr.h1.op1 == 8w0x0) 
             ;
         else 
@@ -158,15 +154,7 @@ control cIngress(inout headers hdr, inou
                                         else 
                                             if (hdr.h1.op1[3:0] == 4w4) 
                                                 hdr_1_h2[4].setInvalid();
-        {
-        }
-        {
-            hdr.h2 = hdr_1_h2;
-        }
-        {
-        }
-        {
-        }
+        hdr.h2 = hdr_1_h2;
         if (hdr.h1.op2 == 8w0x0) 
             ;
         else 
@@ -264,15 +252,7 @@ control cIngress(inout headers hdr, inou
                                         else 
                                             if (hdr.h1.op2[3:0] == 4w4) 
                                                 hdr_1_h2[4].setInvalid();
-        {
-        }
-        {
-            hdr.h2 = hdr_1_h2;
-        }
-        {
-        }
-        {
-        }
+        hdr.h2 = hdr_1_h2;
         if (hdr.h1.op3 == 8w0x0) 
             ;
         else 
@@ -370,11 +350,7 @@ control cIngress(inout headers hdr, inou
                                         else 
                                             if (hdr.h1.op3[3:0] == 4w4) 
                                                 hdr_1_h2[4].setInvalid();
-        {
-        }
-        {
-            hdr.h2 = hdr_1_h2;
-        }
+        hdr.h2 = hdr_1_h2;
         hdr.h1.h2_valid_bits = 8w0;
         if (hdr.h2[0].isValid()) 
             hdr.h1.h2_valid_bits[0:0] = 1w1;
@@ -403,13 +379,11 @@ control uc(inout headers hdr, inout meta
 control DeparserI(packet_out packet, in headers hdr) {
     apply {
         packet.emit<h1_t>(hdr.h1);
-        {
-            packet.emit<h2_t>(hdr.h2[0]);
-            packet.emit<h2_t>(hdr.h2[1]);
-            packet.emit<h2_t>(hdr.h2[2]);
-            packet.emit<h2_t>(hdr.h2[3]);
-            packet.emit<h2_t>(hdr.h2[4]);
-        }
+        packet.emit<h2_t>(hdr.h2[0]);
+        packet.emit<h2_t>(hdr.h2[1]);
+        packet.emit<h2_t>(hdr.h2[2]);
+        packet.emit<h2_t>(hdr.h2[3]);
+        packet.emit<h2_t>(hdr.h2[4]);
         packet.emit<h3_t>(hdr.h3);
     }
 }
