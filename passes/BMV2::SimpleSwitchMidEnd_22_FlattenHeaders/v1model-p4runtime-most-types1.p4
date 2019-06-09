--- before_pass
+++ after_pass
@@ -39,34 +39,35 @@ struct struct1_t {
     bit<9> y;
 }
 header custom_t {
-    Eth0_t          addr0;
-    Eth1_t          addr1;
-    Eth2_t          addr2;
-    bit<8>          e;
-    Custom0_t       e0;
-    Custom1_t       e1;
-    Custom2_t       e2;
-    Custom00_t      e00;
-    Custom01_t      e01;
-    Custom02_t      e02;
-    Custom10_t      e10;
-    Custom11_t      e11;
-    Custom12_t      e12;
-    Custom20_t      e20;
-    Custom21_t      e21;
-    Custom22_t      e22;
-    Custom001_t     e001;
-    Custom002_t     e002;
-    Custom101_t     e101;
-    Custom102_t     e102;
-    Custom201_t     e201;
-    Custom202_t     e202;
-    Custom220_t     e220;
-    Custom0020010_t e0020010;
-    Custom0020020_t e0020020;
-    struct1_t       my_nested_struct1;
-    bit<16>         checksum;
-    bit<8>          s0;
+    bit<48> _addr00;
+    bit<48> _addr11;
+    bit<48> _addr22;
+    bit<8>  _e3;
+    bit<8>  _e04;
+    bit<8>  _e15;
+    bit<8>  _e26;
+    bit<8>  _e007;
+    bit<8>  _e018;
+    bit<8>  _e029;
+    bit<8>  _e1010;
+    bit<8>  _e1111;
+    bit<8>  _e1212;
+    bit<8>  _e2013;
+    bit<8>  _e2114;
+    bit<8>  _e2215;
+    bit<8>  _e00116;
+    bit<8>  _e00217;
+    bit<8>  _e10118;
+    bit<8>  _e10219;
+    bit<8>  _e20120;
+    bit<8>  _e20221;
+    bit<8>  _e22022;
+    bit<8>  _e002001023;
+    bit<8>  _e002002024;
+    bit<7>  _my_nested_struct1_x25;
+    bit<9>  _my_nested_struct1_y26;
+    bit<16> _checksum27;
+    bit<8>  _s028;
 }
 @controller_header("packet_in") header packet_in_header_t {
     bit<8> punt_reason;
@@ -144,63 +145,63 @@ control ingress(inout headers_t hdr, ino
         stdmeta.egress_spec = out_port;
     }
     @name("ingress.set_headers") action set_headers(Eth0_t addr0, Eth1_t addr1, Eth2_t addr2, bit<8> e, Custom0_t e0, Custom1_t e1, Custom2_t e2, Custom00_t e00, Custom01_t e01, Custom02_t e02, Custom10_t e10, Custom11_t e11, Custom12_t e12, Custom20_t e20, Custom21_t e21, Custom22_t e22, Custom001_t e001, Custom002_t e002, Custom101_t e101, Custom102_t e102, Custom201_t e201, Custom202_t e202, Custom220_t e220, Custom0020010_t e0020010, Custom0020020_t e0020020, bit<8> s0) {
-        hdr.custom.addr0 = addr0;
-        hdr.custom.addr1 = addr1;
-        hdr.custom.addr2 = addr2;
-        hdr.custom.e = e;
-        hdr.custom.e0 = e0;
-        hdr.custom.e1 = e1;
-        hdr.custom.e2 = e2;
-        hdr.custom.e00 = e00;
-        hdr.custom.e01 = e01;
-        hdr.custom.e02 = e02;
-        hdr.custom.e10 = e10;
-        hdr.custom.e11 = e11;
-        hdr.custom.e12 = e12;
-        hdr.custom.e20 = e20;
-        hdr.custom.e21 = e21;
-        hdr.custom.e22 = e22;
-        hdr.custom.e001 = e001;
-        hdr.custom.e002 = e002;
-        hdr.custom.e101 = e101;
-        hdr.custom.e102 = e102;
-        hdr.custom.e201 = e201;
-        hdr.custom.e202 = e202;
-        hdr.custom.e220 = e220;
-        hdr.custom.e0020010 = e0020010;
-        hdr.custom.e0020020 = e0020020;
-        hdr.custom.s0 = s0;
+        hdr.custom._addr00 = addr0;
+        hdr.custom._addr11 = addr1;
+        hdr.custom._addr22 = addr2;
+        hdr.custom._e3 = e;
+        hdr.custom._e04 = e0;
+        hdr.custom._e15 = e1;
+        hdr.custom._e26 = e2;
+        hdr.custom._e007 = e00;
+        hdr.custom._e018 = e01;
+        hdr.custom._e029 = e02;
+        hdr.custom._e1010 = e10;
+        hdr.custom._e1111 = e11;
+        hdr.custom._e1212 = e12;
+        hdr.custom._e2013 = e20;
+        hdr.custom._e2114 = e21;
+        hdr.custom._e2215 = e22;
+        hdr.custom._e00116 = e001;
+        hdr.custom._e00217 = e002;
+        hdr.custom._e10118 = e101;
+        hdr.custom._e10219 = e102;
+        hdr.custom._e20120 = e201;
+        hdr.custom._e20221 = e202;
+        hdr.custom._e22022 = e220;
+        hdr.custom._e002001023 = e0020010;
+        hdr.custom._e002002024 = e0020020;
+        hdr.custom._s028 = s0;
     }
     @name("ingress.my_drop") action my_drop() {
     }
     @name("ingress.custom_table") table custom_table_0 {
         key = {
-            hdr.custom.addr0   : exact @name("hdr.custom.addr0") ;
-            hdr.custom.addr1   : exact @name("hdr.custom.addr1") ;
-            hdr.custom.addr2   : exact @name("hdr.custom.addr2") ;
-            hdr.custom.e       : exact @name("hdr.custom.e") ;
-            hdr.custom.e0      : exact @name("hdr.custom.e0") ;
-            hdr.custom.e1      : exact @name("hdr.custom.e1") ;
-            hdr.custom.e2      : exact @name("hdr.custom.e2") ;
-            hdr.custom.e00     : exact @name("hdr.custom.e00") ;
-            hdr.custom.e01     : exact @name("hdr.custom.e01") ;
-            hdr.custom.e02     : exact @name("hdr.custom.e02") ;
-            hdr.custom.e10     : exact @name("hdr.custom.e10") ;
-            hdr.custom.e11     : exact @name("hdr.custom.e11") ;
-            hdr.custom.e12     : exact @name("hdr.custom.e12") ;
-            hdr.custom.e20     : exact @name("hdr.custom.e20") ;
-            hdr.custom.e21     : exact @name("hdr.custom.e21") ;
-            hdr.custom.e22     : exact @name("hdr.custom.e22") ;
-            hdr.custom.e001    : exact @name("hdr.custom.e001") ;
-            hdr.custom.e002    : exact @name("hdr.custom.e002") ;
-            hdr.custom.e101    : exact @name("hdr.custom.e101") ;
-            hdr.custom.e102    : exact @name("hdr.custom.e102") ;
-            hdr.custom.e201    : exact @name("hdr.custom.e201") ;
-            hdr.custom.e202    : exact @name("hdr.custom.e202") ;
-            hdr.custom.e220    : exact @name("hdr.custom.e220") ;
-            hdr.custom.e0020010: exact @name("hdr.custom.e0020010") ;
-            hdr.custom.e0020020: exact @name("hdr.custom.e0020020") ;
-            hdr.custom.s0      : exact @name("hdr.custom.s0") ;
+            hdr.custom._addr00    : exact @name("hdr.custom.addr0") ;
+            hdr.custom._addr11    : exact @name("hdr.custom.addr1") ;
+            hdr.custom._addr22    : exact @name("hdr.custom.addr2") ;
+            hdr.custom._e3        : exact @name("hdr.custom.e") ;
+            hdr.custom._e04       : exact @name("hdr.custom.e0") ;
+            hdr.custom._e15       : exact @name("hdr.custom.e1") ;
+            hdr.custom._e26       : exact @name("hdr.custom.e2") ;
+            hdr.custom._e007      : exact @name("hdr.custom.e00") ;
+            hdr.custom._e018      : exact @name("hdr.custom.e01") ;
+            hdr.custom._e029      : exact @name("hdr.custom.e02") ;
+            hdr.custom._e1010     : exact @name("hdr.custom.e10") ;
+            hdr.custom._e1111     : exact @name("hdr.custom.e11") ;
+            hdr.custom._e1212     : exact @name("hdr.custom.e12") ;
+            hdr.custom._e2013     : exact @name("hdr.custom.e20") ;
+            hdr.custom._e2114     : exact @name("hdr.custom.e21") ;
+            hdr.custom._e2215     : exact @name("hdr.custom.e22") ;
+            hdr.custom._e00116    : exact @name("hdr.custom.e001") ;
+            hdr.custom._e00217    : exact @name("hdr.custom.e002") ;
+            hdr.custom._e10118    : exact @name("hdr.custom.e101") ;
+            hdr.custom._e10219    : exact @name("hdr.custom.e102") ;
+            hdr.custom._e20120    : exact @name("hdr.custom.e201") ;
+            hdr.custom._e20221    : exact @name("hdr.custom.e202") ;
+            hdr.custom._e22022    : exact @name("hdr.custom.e220") ;
+            hdr.custom._e002001023: exact @name("hdr.custom.e0020010") ;
+            hdr.custom._e002002024: exact @name("hdr.custom.e0020020") ;
+            hdr.custom._s028      : exact @name("hdr.custom.s0") ;
         }
         actions = {
             set_output();
@@ -254,12 +255,12 @@ struct tuple_0 {
 }
 control verifyChecksum(inout headers_t hdr, inout metadata_t meta) {
     apply {
-        verify_checksum<tuple_0, bit<16>>(hdr.custom.isValid(), { hdr.custom.addr0, hdr.custom.addr1, hdr.custom.addr2, hdr.custom.e, hdr.custom.e0, hdr.custom.e1, hdr.custom.e2, hdr.custom.e00, hdr.custom.e01, hdr.custom.e02, hdr.custom.e10, hdr.custom.e11, hdr.custom.e12, hdr.custom.e20, hdr.custom.e21, hdr.custom.e22, hdr.custom.e001, hdr.custom.e002, hdr.custom.e101, hdr.custom.e102, hdr.custom.e201, hdr.custom.e202, hdr.custom.e220, hdr.custom.e0020010, hdr.custom.e0020020, hdr.custom.s0 }, hdr.custom.checksum, HashAlgorithm.csum16);
+        verify_checksum<tuple_0, bit<16>>(hdr.custom.isValid(), { hdr.custom._addr00, hdr.custom._addr11, hdr.custom._addr22, hdr.custom._e3, hdr.custom._e04, hdr.custom._e15, hdr.custom._e26, hdr.custom._e007, hdr.custom._e018, hdr.custom._e029, hdr.custom._e1010, hdr.custom._e1111, hdr.custom._e1212, hdr.custom._e2013, hdr.custom._e2114, hdr.custom._e2215, hdr.custom._e00116, hdr.custom._e00217, hdr.custom._e10118, hdr.custom._e10219, hdr.custom._e20120, hdr.custom._e20221, hdr.custom._e22022, hdr.custom._e002001023, hdr.custom._e002002024, hdr.custom._s028 }, hdr.custom._checksum27, HashAlgorithm.csum16);
     }
 }
 control computeChecksum(inout headers_t hdr, inout metadata_t meta) {
     apply {
-        update_checksum<tuple_0, bit<16>>(hdr.custom.isValid(), { hdr.custom.addr0, hdr.custom.addr1, hdr.custom.addr2, hdr.custom.e, hdr.custom.e0, hdr.custom.e1, hdr.custom.e2, hdr.custom.e00, hdr.custom.e01, hdr.custom.e02, hdr.custom.e10, hdr.custom.e11, hdr.custom.e12, hdr.custom.e20, hdr.custom.e21, hdr.custom.e22, hdr.custom.e001, hdr.custom.e002, hdr.custom.e101, hdr.custom.e102, hdr.custom.e201, hdr.custom.e202, hdr.custom.e220, hdr.custom.e0020010, hdr.custom.e0020020, hdr.custom.s0 }, hdr.custom.checksum, HashAlgorithm.csum16);
+        update_checksum<tuple_0, bit<16>>(hdr.custom.isValid(), { hdr.custom._addr00, hdr.custom._addr11, hdr.custom._addr22, hdr.custom._e3, hdr.custom._e04, hdr.custom._e15, hdr.custom._e26, hdr.custom._e007, hdr.custom._e018, hdr.custom._e029, hdr.custom._e1010, hdr.custom._e1111, hdr.custom._e1212, hdr.custom._e2013, hdr.custom._e2114, hdr.custom._e2215, hdr.custom._e00116, hdr.custom._e00217, hdr.custom._e10118, hdr.custom._e10219, hdr.custom._e20120, hdr.custom._e20221, hdr.custom._e22022, hdr.custom._e002001023, hdr.custom._e002002024, hdr.custom._s028 }, hdr.custom._checksum27, HashAlgorithm.csum16);
     }
 }
 V1Switch<headers_t, metadata_t>(ParserImpl(), verifyChecksum(), ingress(), egress(), computeChecksum(), DeparserImpl()) main;
