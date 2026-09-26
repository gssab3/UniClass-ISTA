package it.unisa.uniclass.common.Filter;

import jakarta.servlet.Filter;
import jakarta.servlet.FilterChain;
import jakarta.servlet.ServletException;
import jakarta.servlet.ServletRequest;
import jakarta.servlet.ServletResponse;
import jakarta.servlet.annotation.WebFilter;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import java.io.IOException;

@WebFilter("/*")
public class SecurityHeadersFilter implements Filter {
    @Override
    public void doFilter(ServletRequest request, ServletResponse response, FilterChain chain) throws IOException, ServletException {
        HttpServletRequest req = (HttpServletRequest) request;
        HttpServletResponse res = (HttpServletResponse) response;
        res.setHeader("X-Content-Type-Options", "nosniff");
        String path = req.getRequestURI();
        boolean api = path.endsWith("/getResto")
                || path.endsWith("/getAnno")
                || path.endsWith("/GetEmailServlet")
                || path.endsWith("/GetAttivati")
                || path.endsWith("/GetNonAttivati");
        if (api) {
            res.setHeader("Content-Security-Policy", "sandbox");
            String dest = req.getHeader("Sec-Fetch-Dest");
            if (dest != null && (dest.equals("document") || dest.equals("iframe") || dest.equals("object") || dest.equals("embed"))) {
                res.sendError(HttpServletResponse.SC_FORBIDDEN);
                return;
            }
        }
        chain.doFilter(request, response);
    }
}
