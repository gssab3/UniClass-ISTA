package it.unisa.uniclass.utenti.controller;

import it.unisa.uniclass.common.exceptions.AuthenticationException;
import it.unisa.uniclass.common.security.CredentialSecurity;
import it.unisa.uniclass.utenti.model.Accademico;
import it.unisa.uniclass.utenti.model.Utente;
import it.unisa.uniclass.utenti.service.UserDirectory; // IMPORTA L'INTERFACCIA
import jakarta.ejb.EJB;
import jakarta.servlet.annotation.WebServlet;
import jakarta.servlet.http.HttpServlet;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import jakarta.servlet.http.HttpSession;

import java.io.IOException;

@WebServlet(name = "loginServlet", value = "/Login")
public class LoginServlet extends HttpServlet {

    // SOSTITUZIONE: Uso UserDirectory invece di UtenteService
    @EJB
    private UserDirectory userDirectory;

    @Override
    public void doGet(HttpServletRequest request, HttpServletResponse response) {
        doPost(request, response);
    }

    @Override
    public void doPost(HttpServletRequest request, HttpServletResponse response) {
        try {
            String email = request.getParameter("email");
            String passwordRaw = request.getParameter("password");
            String password = passwordRaw; // niente hash


            try {
                // CHIAMATA FACADE
                Utente user = userDirectory.login(email, password);

                // Logica di controllo attivazione (Business Logic specifica del Controller o delegabile)
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