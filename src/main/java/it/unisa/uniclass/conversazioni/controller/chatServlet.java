package it.unisa.uniclass.conversazioni.controller;

import it.unisa.uniclass.conversazioni.model.Messaggio;
import it.unisa.uniclass.conversazioni.service.MessaggioService;
import it.unisa.uniclass.utenti.model.Accademico;
import it.unisa.uniclass.utenti.service.UserDirectory;
import jakarta.ejb.EJB;
import jakarta.servlet.ServletException;
import jakarta.servlet.annotation.WebServlet;
import jakarta.servlet.http.HttpServlet;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import jakarta.servlet.http.HttpSession;

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

@WebServlet(name = "chatServlet", value = "/chatServlet")
public class chatServlet extends HttpServlet {

    @EJB
    private MessaggioService messaggioService;

    @EJB
    private UserDirectory userDirectory;

    @Override
    public void doGet(HttpServletRequest req, HttpServletResponse resp) {
        try {
            HttpSession session = req.getSession();

            String emailDest = req.getParameter("accademico");
            String emailSelf = req.getParameter("accademicoSelf");

            Accademico accademicoDest = userDirectory.getAccademico(emailDest);
            Accademico accademicoSelf = userDirectory.getAccademico(emailSelf);

            if (accademicoDest == null || accademicoSelf == null) {
                throw new ServletException("Utenti non validi o non accademici.");
            }

            List<Messaggio> tuttiMessaggi = messaggioService.trovaTutti();

            List<Messaggio> messaggiInviati = new ArrayList<>();
            List<Messaggio> messaggiRicevuti = new ArrayList<>();

            for (Messaggio messaggio : tuttiMessaggi) {
                if (messaggio.getDestinatario() != null &&
                        messaggio.getDestinatario().getMatricola().equals(accademicoSelf.getMatricola())) {
                    messaggiRicevuti.add(messaggio);
                }
                if (messaggio.getAutore() != null &&
                        messaggio.getAutore().getMatricola().equals(accademicoSelf.getMatricola())) {
                    messaggiInviati.add(messaggio);
                }
            }

            // 🔥 FIX: inizializzazione relazioni LAZY
            for (Messaggio m : tuttiMessaggi) {
                if (m.getAutore() != null) m.getAutore().getNome();
                if (m.getDestinatario() != null) m.getDestinatario().getNome();
                if (m.getTopic() != null) m.getTopic().getNome();
            }

            req.setAttribute("messaggigi", tuttiMessaggi);
            session.setAttribute("messaggigi", tuttiMessaggi);

            req.setAttribute("messaggiInviati", messaggiInviati);
            req.setAttribute("messaggiRicevuti", messaggiRicevuti);

            req.setAttribute("accademico", accademicoDest);
            session.setAttribute("accademico", accademicoDest);

            session.setAttribute("accademicoSelf", accademicoSelf);
            req.setAttribute("accdemicoSelf", accademicoSelf);

            resp.sendRedirect(req.getContextPath() + "/chat.jsp");

        } catch (Exception e) {
            req.getServletContext().log("Error processing chat request", e);
            try {
                resp.sendError(HttpServletResponse.SC_INTERNAL_SERVER_ERROR);
            } catch (IOException ignored) {}
        }
    }

    @Override
    public void doPost(HttpServletRequest req, HttpServletResponse resp) throws ServletException, IOException {
        doGet(req, resp);
    }
}
