package it.unisa.uniclass.testing.unit.utenti.service.dao;

import it.unisa.uniclass.utenti.model.Accademico;
import it.unisa.uniclass.utenti.service.dao.AccademicoDAO;
import jakarta.persistence.EntityManager;
import jakarta.persistence.TypedQuery;
import jakarta.persistence.NoResultException;
import jakarta.persistence.PersistenceException;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.util.Collections;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.Mockito.*;

class AccademicoDAOTest {

    private EntityManager em;
    private TypedQuery<Accademico> accademicoQuery;
    private TypedQuery<String> stringQuery;
    private AccademicoDAO dao;

    @BeforeEach
    void setUp() {
        em = mock(EntityManager.class);
        accademicoQuery = mock(TypedQuery.class);
        stringQuery = mock(TypedQuery.class);

        dao = new AccademicoDAO();

        // Iniettiamo il mock dell'EntityManager via reflection
        try {
            var field = AccademicoDAO.class.getDeclaredField("emUniclass");
            field.setAccessible(true);
            field.set(dao, em);
        } catch (Exception e) {
            throw new RuntimeException(e);
        }
    }

    @Test
    void testTrovaAccademicoUniClass_Success() {
        Accademico a = new Accademico();
        when(em.createNamedQuery(Accademico.TROVA_ACCADEMICO, Accademico.class)).thenReturn(accademicoQuery);
        when(accademicoQuery.setParameter("matricola", "123")).thenReturn(accademicoQuery);
        when(accademicoQuery.getSingleResult()).thenReturn(a);

        assertEquals(a, dao.trovaAccademicoUniClass("123"));
    }

    @Test
    void testTrovaAccademicoUniClass_PersistenceException() {
        when(em.createNamedQuery(Accademico.TROVA_ACCADEMICO, Accademico.class)).thenReturn(accademicoQuery);
        when(accademicoQuery.setParameter("matricola", "123")).thenReturn(accademicoQuery);
        when(accademicoQuery.getSingleResult()).thenThrow(new PersistenceException());

        assertNull(dao.trovaAccademicoUniClass("123"));
    }

    @Test
    void testTrovaTuttiUniClass() {
        List<Accademico> list = Collections.singletonList(new Accademico());
        when(em.createNamedQuery(Accademico.TROVA_TUTTI, Accademico.class)).thenReturn(accademicoQuery);
        when(accademicoQuery.getResultList()).thenReturn(list);

        assertEquals(list, dao.trovaTuttiUniClass());
    }

    @Test
    void testTrovaEmailUniClass_Success() {
        Accademico a = new Accademico();
        when(em.createNamedQuery(Accademico.TROVA_EMAIL, Accademico.class)).thenReturn(accademicoQuery);
        when(accademicoQuery.setParameter("email", "x@y.com")).thenReturn(accademicoQuery);
        when(accademicoQuery.getSingleResult()).thenReturn(a);

        assertEquals(a, dao.trovaEmailUniClass("x@y.com"));
    }

    @Test
    void testTrovaEmailUniClass_NoResult() {
        when(em.createNamedQuery(Accademico.TROVA_EMAIL, Accademico.class)).thenReturn(accademicoQuery);
        when(accademicoQuery.setParameter("email", "x@y.com")).thenReturn(accademicoQuery);
        when(accademicoQuery.getSingleResult()).thenThrow(new NoResultException());

        assertNull(dao.trovaEmailUniClass("x@y.com"));
    }

    @Test
    void testTrovaAttivati() {
        List<Accademico> list = Collections.singletonList(new Accademico());
        when(em.createNamedQuery(Accademico.TROVA_ATTIVATI, Accademico.class)).thenReturn(accademicoQuery);
        when(accademicoQuery.setParameter("attivato", true)).thenReturn(accademicoQuery);
        when(accademicoQuery.getResultList()).thenReturn(list);

        assertEquals(list, dao.trovaAttivati(true));
    }

    @Test
    void testAggiungiAccademico() {
        Accademico a = new Accademico();
        dao.aggiungiAccademico(a);
        verify(em).merge(a);
    }

    @Test
    void testRimuoviAccademico() {
        Accademico a = new Accademico();
        dao.rimuoviAccademico(a);
        verify(em).remove(a);
    }

    @Test
    void testRetrieveEmail() {
        List<String> emails = Collections.singletonList("x@y.com");
        when(em.createNamedQuery(Accademico.RETRIEVE_EMAIL, String.class)).thenReturn(stringQuery);
        when(stringQuery.getResultList()).thenReturn(emails);

        assertEquals(emails, dao.retrieveEmail());
    }

    @Test
    void testCambiaAttivazione() {
        Accademico a = new Accademico();
        dao.cambiaAttivazione(a, true);
        assertTrue(a.isAttivato());
        verify(em).merge(a);
    }
}
