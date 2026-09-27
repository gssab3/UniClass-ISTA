package it.unisa.uniclass.utenti.controller;

import it.unisa.uniclass.common.Utils;
import it.unisa.uniclass.common.exceptions.AuthenticationException;
import it.unisa.uniclass.common.security.CSRF;
import it.unisa.uniclass.common.security.CredentialSecurity;
import it.unisa.uniclass.common.security.LoginRateLimiter;
import it.unisa.uniclass.utenti.model.Accademico;
import it.unisa.uniclass.utenti.model.Utente;
import it.unisa.uniclass.utenti.service.UserDirectory;
import jakarta.ejb.EJB;
import jakarta.servlet.annotation.WebServlet;
import jakarta.servlet.http.HttpServlet;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import jakarta.servlet.http.HttpSession;

import java.io.IOException;

@WebServlet(name = "loginServlet", value = "/Login")
public class LoginServlet extends HttpServlet {

    @EJB
    private UserDirectory userDirectory;

    @Override
    public void doGet(HttpServletRequest request, HttpServletResponse response) {
        try {
            response.sendRedirect(request.getContextPath() + "/Login.jsp");
        } catch (IOException ignored) {}
    }

    @Override
    public void doPost(HttpServletRequest request, HttpServletResponse response) {
        try {
            String email = request.getParameter("email");
            String passwordRaw = request.getParameter("password");
            String password = passwordRaw;
            String rateKey = LoginRateLimiter.key(request.getRemoteAddr(), email);

            if (LoginRateLimiter.isBlocked(rateKey)) {
                response.sendRedirect(request.getContextPath() + "/Login.jsp?action=blocked");
                return;
            }

            if (!CSRF.isValid(request)) {
                response.sendError(HttpServletResponse.SC_FORBIDDEN);
                return;
            }

            if (!Utils.isEmail(email) || passwordRaw == null || passwordRaw.length() < 8 || passwordRaw.length() > 20) {
                LoginRateLimiter.recordFailure(rateKey);
                response.sendRedirect(request.getContextPath() + "/Login.jsp?action=error");
                return;
            }


            try {
                Utente user = userDirectory.login(email, password);
                LoginRateLimiter.reset(rateKey);

                if (user instanceof Accademico) {
                    Accademico acc = (Accademico) user;
                    if (!acc.isAttivato()) {
                        response.sendRedirect(request.getContextPath() + "/Login.jsp?action=notactivated");
                        return;
                    }
                }

                HttpSession session = request.getSession(true);
                session.setAttribute("currentSessionUser", user);
                session.setAttribute("utenteEmail", user.getEmail());

                response.sendRedirect(request.getContextPath() + "/Home");

            } catch (AuthenticationException e) {
                LoginRateLimiter.recordFailure(rateKey);
                response.sendRedirect(request.getContextPath() + "/Login.jsp?action=error");
            }

        } catch (IOException e) {
            request.getServletContext().log("Error processing login request", e);
            try {
                response.sendRedirect(request.getContextPath() + "/Login.jsp?action=error");
            } catch (IOException ignored) {}
        }
    }
}