package it.unisa.uniclass.testing.unit.conversazioni.controller;

import it.unisa.uniclass.conversazioni.controller.chatServlet;
import it.unisa.uniclass.conversazioni.model.Messaggio;
import it.unisa.uniclass.conversazioni.model.Topic;
import it.unisa.uniclass.conversazioni.service.MessaggioService;
import it.unisa.uniclass.utenti.model.Accademico;
import it.unisa.uniclass.utenti.service.UserDirectory;
import jakarta.servlet.ServletContext;
import jakarta.servlet.ServletException;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import jakarta.servlet.http.HttpSession;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;
import org.mockito.junit.jupiter.MockitoSettings;
import org.mockito.quality.Strictness;

import java.io.IOException;
import java.lang.reflect.Field;
import java.util.ArrayList;
import java.util.List;

import static org.mockito.ArgumentMatchers.*;
import static org.mockito.Mockito.*;

@ExtendWith(MockitoExtension.class)
@MockitoSettings(strictness = Strictness.LENIENT)

class ChatServletTest {

    private chatServlet servlet;

    @Mock private HttpServletRequest request;
    @Mock private HttpServletResponse response;
    @Mock private HttpSession session;
    @Mock private ServletContext servletContext;
    @Mock private MessaggioService messaggioService;
    @Mock private UserDirectory userDirectory;

    @BeforeEach
    void setUp() throws Exception {
        servlet = new chatServlet();

        Field f1 = chatServlet.class.getDeclaredField("messaggioService");
        f1.setAccessible(true);
        f1.set(servlet, messaggioService);

        Field f2 = chatServlet.class.getDeclaredField("userDirectory");
        f2.setAccessible(true);
        f2.set(servlet, userDirectory);

        when(request.getSession()).thenReturn(session);
        when(request.getServletContext()).thenReturn(servletContext);
        lenient().when(request.getContextPath()).thenReturn("/ctx");
    }

    @Test
    @DisplayName("DoGet: Successo completo con tutti i branch coperti")
    void testDoGet_FullSuccess() throws IOException {

        String emailSelf = "self@unisa.it";
        String emailDest = "dest@unisa.it";

        when(request.getParameter("accademico")).thenReturn(emailDest);
        when(request.getParameter("accademicoSelf")).thenReturn(emailSelf);

        Accademico self = mock(Accademico.class);
        when(self.getMatricola()).thenReturn("111");
        when(self.getNome()).thenReturn("Self");

        Accademico dest = mock(Accademico.class);
        when(dest.getMatricola()).thenReturn("222");
        when(dest.getNome()).thenReturn("Dest");

        when(userDirectory.getAccademico(emailSelf)).thenReturn(self);
        when(userDirectory.getAccademico(emailDest)).thenReturn(dest);

        List<Messaggio> all = new ArrayList<>();

        // Messaggio ricevuto
        Messaggio ricevuto = new Messaggio();
        ricevuto.setDestinatario(self);
        ricevuto.setAutore(dest);
        Topic topic = new Topic();
        topic.setNome("T1");
        ricevuto.setTopic(topic);
        all.add(ricevuto);

        // Messaggio inviato
        Messaggio inviato = new Messaggio();
        inviato.setAutore(self);
        inviato.setDestinatario(dest);
        all.add(inviato);

        // Messaggio con tutto null (copre rami false)
        Messaggio nullo = new Messaggio();
        all.add(nullo);

        when(messaggioService.trovaTutti()).thenReturn(all);

        servlet.doGet(request, response);

        verify(request).setAttribute("messaggigi", all);
        verify(session).setAttribute("messaggigi", all);

        verify(request).setAttribute(eq("messaggiInviati"), any());
        verify(request).setAttribute(eq("messaggiRicevuti"), any());

        verify(request).setAttribute("accademico", dest);
        verify(session).setAttribute("accademico", dest);

        verify(session).setAttribute("accademicoSelf", self);
        verify(request).setAttribute("accdemicoSelf", self); // typo voluto nel codice

        verify(response).sendRedirect("/ctx/chat.jsp");
    }

    @Test
    @DisplayName("DoGet: Utenti null → ramo eccezione")
    void testDoGet_InvalidUsers() throws IOException {

        when(request.getParameter(anyString())).thenReturn("x");
        when(userDirectory.getAccademico(anyString())).thenReturn(null);

        servlet.doGet(request, response);

        verify(servletContext).log(eq("Error processing chat request"), any(Exception.class));
        verify(response).sendError(HttpServletResponse.SC_INTERNAL_SERVER_ERROR);

        verify(messaggioService, never()).trovaTutti();
    }

    @Test
    @DisplayName("DoGet: Eccezione runtime nel service")
    void testDoGet_RuntimeException() throws IOException {

        when(request.getParameter(anyString())).thenReturn("x");

        Accademico acc = new Accademico();
        acc.setMatricola("1");

        when(userDirectory.getAccademico(anyString())).thenReturn(acc);
        when(messaggioService.trovaTutti()).thenThrow(new RuntimeException("boom"));

        servlet.doGet(request, response);

        verify(servletContext).log(eq("Error processing chat request"), any(RuntimeException.class));
        verify(response).sendError(HttpServletResponse.SC_INTERNAL_SERVER_ERROR);
    }

    @Test
    @DisplayName("DoPost: delega correttamente a DoGet")
    void testDoPost() throws IOException, ServletException {

        when(request.getParameter(anyString())).thenReturn("x");
        when(userDirectory.getAccademico(anyString())).thenReturn(null);

        servlet.doPost(request, response);

        verify(servletContext).log(eq("Error processing chat request"), any(Exception.class));
        verify(response).sendError(HttpServletResponse.SC_INTERNAL_SERVER_ERROR);
    }
}
