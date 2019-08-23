--- before_pass
+++ after_pass
@@ -159,9 +159,6 @@ parser ParserImpl(packet_in packet, out
         hdr.tcp_options_vec[9].s.setInvalid();
         hdr.tcp_options_vec[9].sack.setInvalid();
         hdr.tcp_options_padding.setInvalid();
-        transition Tcp_option_parser_start;
-    }
-    state Tcp_option_parser_start {
         verify(hdr.tcp.dataOffset >= 4w5, error.TcpDataOffsetTooSmall);
         Tcp_option_parser_tcp_hdr_bytes_left = (bit<7>)(hdr.tcp.dataOffset + 4w11) << 2;
         transition Tcp_option_parser_next_option;
