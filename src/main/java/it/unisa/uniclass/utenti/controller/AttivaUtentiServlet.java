package it.unisa.uniclass.utenti.controller;

import it.unisa.uniclass.common.security.CredentialSecurity;
import it.unisa.uniclass.common.security.PasswordGenerator;
import it.unisa.uniclass.utenti.model.Accademico;
import it.unisa.uniclass.utenti.model.Ruolo; // Assumo si usi Ruolo ora
import it.unisa.uniclass.utenti.model.Utente;
import it.unisa.uniclass.utenti.service.UtenteService;
import jakarta.ejb.EJB;
import jakarta.servlet.annotation.WebServlet;
import jakarta.servlet.http.HttpServlet;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;

import java.io.IOException;

@WebServlet(name = "AttivaUtentiServlet", value = "/AttivaUtentiServlet")
public class AttivaUtentiServlet extends HttpServlet {

    @EJB
    private UtenteService utenteService;

    @Override
    protected void doPost(HttpServletRequest req, HttpServletResponse resp) {
        try {
            String param = req.getParameter("param");

            if ("add".equals(param)) {
                String email = req.getParameter("email");
                String matricola = req.getParameter("matricola");
                String ruoloReq = req.getParameter("tipo"); // Stringa dalla view (es. "Studente")

                Utente utente = utenteService.getUtenteByEmail(email);

                if (utente instanceof Accademico) {
                    Accademico acc = (Accademico) utente;

                    // Verifica corrispondenza matricola e ruolo
                    // Nota: Qui bisognerebbe mappare la stringa ruoloReq all'Enum Ruolo
                    boolean ruoloMatch = false;
                    if (acc.getRuolo() != null && acc.getRuolo().toString().equalsIgnoreCase(ruoloReq)) {
                        ruoloMatch = true;
                    }

                    if (acc.getMatricola().equals(matricola) && ruoloMatch) {
                        String password = PasswordGenerator.generatePassword(8);

                        acc.setAttivato(true);
                        acc.setPassword(CredentialSecurity.hashPassword(password));

                        // Il metodo aggiornaUtente nel service gestisce il merge
                        utenteService.aggiornaUtente(acc);

                        System.out.println("Utente attivato. Password generata: " + password);
                        resp.sendRedirect(req.getContextPath() + "/PersonaleTA/AttivaUtenti.jsp");
                    } else {
                        resp.sendRedirect(req.getContextPath() + "/PersonaleTA/AttivaUtenti.jsp?action=error");
                    }
                } else {
                    // Non trovato o non accademico
                    resp.sendRedirect(req.getContextPath() + "/PersonaleTA/AttivaUtenti.jsp?action=error");
                }

            } else if ("remove".equals(param)) {
                String email = req.getParameter("email-remove");
                Utente utente = utenteService.getUtenteByEmail(email);

                if (utente instanceof Accademico) {
                    Accademico acc = (Accademico) utente;
                    acc.setAttivato(false);
                    utenteService.aggiornaUtente(acc);
                }
                resp.sendRedirect(req.getContextPath() + "/PersonaleTA/AttivaUtenti.jsp");
            }
        } catch (Exception e) {
            req.getServletContext().log("Error processing user activation", e);
            try {
                resp.sendError(HttpServletResponse.SC_INTERNAL_SERVER_ERROR);
            } catch (IOException ignored) {}
        }
    }

    @Override
    protected void doGet(HttpServletRequest req, HttpServletResponse resp) {
        doPost(req, resp);
    }
}